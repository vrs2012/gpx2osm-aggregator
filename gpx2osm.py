#!/usr/bin/python
# gpx2osm-aggregator
# by vrs2012 (@github)
# GPLv3
# 
# purpose - take gpx files with lot of tracks, aggregate them into (more)usable OSM ways. 
# 
# input - actual gpx trace files (contain lot of tracks... i.e. same 
#                                 road traversed 1..200 times)
# process - unify many close running tracks into one way. 
# output - osm file with highway=road geometries. 
# 
# Basic data structures:
#      node -  
#          x,y = metric coordinate. lat,lon is converted to approximate meters on import, and back on export
#          edges = set of edges that use this node
#      edge -
#          node1,node2 = start and end points. edges are oriented, but can be fliped at any time for easier processing. 
#          len = length in meters for the edge
#          mass = total vehicle meters into this edge (combining edges increase mass)
#      map - container of data
#          edges - container of all edges in map.
#          nodes - all _used_ nodes in map. 
#          grid  - indexed nodes. (50m-sized cells, for faster lookup of nodes near edge or node) 

import sys
import time
import math
import collections
import optparse
import glob
import xml.etree.ElementTree as ET
sys.setrecursionlimit(100000)
FILEMASK = './*.gpx'
OUTFILE= 'out.osm'
DEBUG=1
CHKDIST = 200.0 # when deciding if two tracks run parrallel - how many meters to check
MPERLAT = 111000.0 # metres per degree latitude
MPERLON = 111000.0 # meters per degree longitude (this is adjusted from first lon reading in import)


# ==================== DATA =========================        
class Node(object):
    __slot__=['x','y','edges','idx']
    global map
    def __init__(self,x,y):
        self.x = x
        self.y = y
        self.edges = set()
        self.idx = long(x/map.gridsize)*1000000 + long(y/map.gridsize) 
        
    def __repr__(self): 
        return 'xy=%s %s' % (round(self.x,1) , round(self.y, 1))

    def next(self, node=None):
        # returns exit if there is single (for building continuous way)
        if node:
            for e in self.edges: 
                if e.node1 == self and e.node2 == node: return e
                #if e.node1 == node and e.node2 == self: e.flip(); return e
            return None
        edges_out = [e for e in self.edges if e.node1 == self]
        edges_in = [e for e in self.edges if e.node2 == self]
        if len(edges_in)==1 and len(edges_out)==1: return edges_out[0]
        return None
            
    def add_edge(self,edge):
        self.edges.add(edge)
        map.nodes.add(self)
        map.grid[self.idx].add(self)
        
    def remove_edge(self,edge):
        self.edges.remove(edge)
        if not self.edges: 
            map.nodes.remove(self)
            map.grid[self.idx].remove(self)

    def xy_update(self):
        if self.idx in map.grid and self in map.grid[self.idx]:
            map.grid[self.idx].remove(self)
        self.idx = long(self.x/map.gridsize)*1000000 + long(self.y/map.gridsize)
        map.grid[self.idx].add(self)
        for e in list(self.edges):
            e.len = e.node1-e.node2
            if e.len<=0.01: e.node1.merge(e.node2) 
       
    def vector(self,node2):
        # return vector in radians 
        dy = node2.y - self.y
        dx = node2.x - self.x
        hip = math.sqrt(dy*dy+dx*dx)
        asin = math.asin(abs(dy)/hip)
        if dx*dy<0: asin = math.pi-asin
        if dy<0: asin = asin + math.pi
        return asin

    def kill(self):
        for e in list(self.edges): e.kill()

    
    def move_to_edge(self,nodeA,nodeB):
        # moves this node (C) closer to A-B line. See notes about algorithm.
        
        # find point D = imaginary point on A-B, closest to C
        CA = self- nodeA
        AB = nodeA - nodeB
        CB = self- nodeB
        CD = C_from_AB(AB,CA,CB)
        if CD < 0.1: return # no moving - C is on or almost on AB.
        AD = math.sqrt(CA*CA-CD*CD)
        if AD < 0.1: 
            nodeD = Node( nodeA.x, nodeA.y)
        else:
            vectorAB = nodeA.vector(nodeB)
            nodeD = Node(nodeA.x + math.cos(vectorAB) * AD,
                         nodeA.y + math.sin(vectorAB) * AD)
        
        # calculate travel of C if we would move it whole way to AB
        # C will be moved part of that distance, A,B will be moved opposite direction
        delta_x = (nodeD.x - self.x) 
        delta_y = (nodeD.y - self.y)

        # see notes about formulas!
        COEF = AD / AB
        MA = sum([e.mass for e in nodeA.edges]) # mass of node A
        MB = sum([e.mass for e in nodeB.edges])
        MC = sum([e.mass for e in self.edges])
        if COEF >0.99: COEF = 0.99
        if COEF <0.01: COEF = 0.01
        # C vs A coef: how much more heavier is C vs A. 
        COEF_CA = (1.0-COEF)*MC / ( (1.0-COEF)*MC + MA)
        COEF_CB = COEF*MC / ( COEF*MC + MB)
        self.x += delta_x * (1.0-COEF_CA) * (1.0-COEF)
        self.y += delta_y * (1.0-COEF_CA) * (1.0-COEF)
        nodeA.x -= delta_x * (COEF_CA) * (1.0-COEF)
        nodeA.y -= delta_y * (COEF_CA) * (1.0-COEF)
        self.x += delta_x * (1.0-COEF_CB) * (COEF)
        self.y += delta_y * (1.0-COEF_CB) * (COEF)
        nodeB.x -= delta_x * (COEF_CB) * (COEF)
        nodeB.y -= delta_y * (COEF_CB) * (COEF)
        self.xy_update()
        nodeA.xy_update()
        nodeB.xy_update()
        
    def __sub__(self, o):
        xd = self.x - o.x
        yd = self.y - o.y
        return math.sqrt(xd * xd + yd * yd)
    
    def nodes_within(self,dist,edges_tested=None):
        # return points that can be traveled from this node, exactly at dist
        if edges_tested == None: edges_tested = set()
        nodes = []
        for edge in self.edges:
            if edge in edges_tested: continue
            edges_tested.add(edge)
            if edge.node1==self: B = edge.node2
            else: B = edge.node1
            if abs(edge.len-dist)<1.0:
                nodes.append(B)
                continue
            if edge.len>dist:
                coef = dist/edge.len
                end_point = Node(self.x + (B.x - self.x)*coef, self.y + (B.y - self.y)*coef)
                nodes.append(end_point)
                continue
            nodes +=  B.nodes_within(dist-edge.len,edges_tested)
            
        return nodes

    
    def merge(self,B):
        # merge two nodes in one. B is the "other node"
        if self==B: return self

        # step 1 - calculate average point for new centre node
        A_w = 0.1 + sum([e.mass for e in self.edges])
        B_w = 0.1 + sum([e.mass for e in self.edges])
        self.x += (B.x-self.x)*A_w/(A_w+B_w)
        self.y += (B.y-self.y)*A_w/(A_w+B_w)
        self.xy_update()
        
        for edge in list(B.edges):
            n1,n2 = edge.node1, edge.node2
            if n1 == B: n1 = self
            else: n2 = self
            if n1==n2: 
                edge.kill() 
                continue
            
            if n1-n2 > 0.5: 
                new_edge = map.find_or_create_edge(n1,n2)
                new_edge.add_mass(edge)
                edge.kill()
                continue
            # n1-n2 is very small - merge them
            edge.kill()
            n1.merge(n2)
        return self
                                
class Edge(object):
    __slot__=['node1','node2','len','mass','direction','w']
    global map
    def __init__(self, node1, node2, mass=1.0):
        if node1 == node2: raise Exception, "sames nodes"
        if node1.x == node2.x and node1.y == node2.y: raise Exception, "can't have zero len edges"
        self.node1 = node1
        self.node2 = node2
        self.len = self.node1 - self.node2
        self.mass = self.len 
        self.direction = 1.0
        self.node1.add_edge(self)
        self.node2.add_edge(self)
        map.edges.add(self)
        self.w = 1.0
        
    def add_mass(self, edge, coef=1.0):
        mass_fw = self.mass * self.direction + coef * edge.mass * edge.direction
        mass_bk = self.mass * (1.0 - self.direction) + coef * edge.mass * (1.0 - edge.direction)
        self.mass = mass_fw + mass_bk
        self.direction = mass_fw / self.mass
        
        self.w = max(1.0,(self.mass)/self.len)
        
    def kill(self):
        self.node1.remove_edge(self)
        self.node2.remove_edge(self)
        map.edges.remove(self)
        
    def __repr__(self):
        return 'E(%s(%s)%s,  %s - %s)' % (round(self.len,1), round(self.mass,1), id(self),self.node1, self.node2)

    def split(self,mid_node):
        m_node1 = mid_node-self.node1
        m_node2 = mid_node-self.node2
        if m_node1 < 0.1: 
            mid_node.merge(self.node1)
            return
        if m_node2 < 0.1:
            mid_node.merge(self.node2)
            return
        coef = m_node1 / (m_node1 + m_node2)
        edge1 = map.find_or_create_edge(self.node1, mid_node)
        edge2 = map.find_or_create_edge(mid_node, self.node2)
        edge1.add_mass (self, coef)
        edge2.add_mass (self, 1.0-coef)
        self.kill()
        
    def next(self, back = False):
        if back: node_exit = self.node1
        else: node_exit = self.node2
        edges_connected = [e for e in node_exit.edges if e != self]
        if len(edges_connected)!=1: return None
        edge_exit = edges_connected[0]
        if not back and edge_exit.node2 == node_exit: edge_exit.flip()
        if back and edge_exit.node1 == node_exit: edge_exit.flip()
        return edge_exit
        
    def get_segment(self):
        # return list with edges between intersections
        ret=[self]
        while True:
            enext = ret[-1].next()
            if not enext or enext in ret: break
            ret.append(enext)
        while True:
            enext = ret[0].next(True)
            if not enext or enext in ret: break
            ret.insert(0,enext)
        return ret

    def flip(self):
        self.node1, self.node2 = self.node2, self.node1
        self.direction = 1.0 - self.direction
        
class Map(object):
    edges = set()
    nodes = set()
    grid = collections.defaultdict(set)
    gridsize = 50.0    
    def find_or_create_edge(self,node1,node2):
        for e in node1.edges:
            if e.node1 == node1 and e.node2 == node2: return e
            if e.node2 == node1 and e.node1 == node2: e.flip(); return e
        e = Edge(node1, node2)
        e.mass = 0.0
        return e

    def __repr__(self):
        return 'data: edges:%s, nodes in grid %s' % (len(self.edges),len(self.nodes))
            
    def remove_untraveled_edges(self, minmass=2.1):
        if DEBUG: print 'REMOVE untraveled...'
        edges_tested = set()
        cnt = 0
        for e in list(map.edges):
            if e in edges_tested: continue
            seg = e.get_segment()
            edges_tested.update(set(seg))
            l = len(seg)
            w = sum([e.w for e in seg])
            segment_mass = w/l
            if segment_mass < minmass:
                cnt+= len(seg)
                for e in seg: e.kill()
        if DEBUG: print 'removed untraveled (<%s): %s' % (minmass,cnt)

    def nodes_around_edge2(self, edge, radius):
        # return nodesids that are close to this edge. 
        # consider quadrant with min.max idx
        x1,y1=(int(edge.node1.x/self.gridsize),int(edge.node1.y/self.gridsize))
        x2,y2=(int(edge.node2.x/self.gridsize),int(edge.node2.y/self.gridsize))
        xidxmax = max(x1,x2)+1
        xidxmin = min(x1,x2)-1
        yidxmax = max(y1,y2)+1
        yidxmin = min(y1,y2)-1
        valid_nodes = {}
                            
        for x_idx in range(xidxmin,xidxmax+1):
            for y_idx in range(yidxmin,yidxmax+1):
                kidx = long(x_idx*1000000) + y_idx
                if kidx not in self.grid: continue
                for node in self.grid[kidx]:
                    if node==edge.node1 or node==edge.node2: continue
                    CA = node-edge.node1
                    CB = node-edge.node2
                    h = C_from_AB(edge.len,CA,CB)
                    if h>radius: continue

                    a = h * h + edge.len * edge.len
                    if CA * CA > a: continue
                    if CB * CB > a: continue
                    
                    valid_nodes[node]=h
        return sorted(valid_nodes, key=valid_nodes.get)
        
    
map = Map()

# ====== IMPORT EXPORT DEF =================================
def xy_from_latlon(lat, lon):
    return float(lon) * MPERLON, float(lat) * MPERLAT
def latlon_from_xy(x,y):
    return y / MPERLAT, x / MPERLON
def insert_namespace(xpath):
    # Enable *simple* xpath searches by inserting the fscking namespace.
    if XMLNS: 
        return '/'.join('{{{0}}}{1}'.format(XMLNS, n) for n in xpath.split('/'))
    else:
        return xpath
def find(et, xpath):
    return et.find(insert_namespace(xpath))
def findall(et, xpath):
    return et.findall(insert_namespace(xpath))
def uri_from_elem(elem):
    if elem.tag[0] == "{":
        uri = elem.tag[1:].partition("}")[0]
    else:
        uri = None
    return uri
XMLNS = None

def import_file(filename):
    # map = storage
    global XMLNS
    print 'IMPORT ' + filename , '...',
    t = ET.ElementTree().parse(filename)
    XMLNS = uri_from_elem(t)
    firstpoint = find(t, 'trk/trkseg/trkpt')
    lat = float(firstpoint.attrib['lat'])
    MPERLON = math.cos(lat / 180.0 * math.pi) * MPERLAT
    for s in findall(t, 'trk/trkseg'):
        prev_node =None
        for p in findall(s,'trkpt'):
            x,y = xy_from_latlon(p.attrib['lat'], p.attrib['lon'])
            cur_node = Node(x,y)
            if prev_node:
                if cur_node.x == prev_node.x and cur_node.y == prev_node.y:
                    continue
                Edge(prev_node, cur_node)
            prev_node = cur_node
    print 'edges=',len(map.edges), 'nodes=',len(map.nodes)
    
def export_to_osm(filename=OUTFILE):
    print 'EXPORT TO',filename,'.n=%s e=%s..' % (len(map.nodes),len(map.edges)),
    f = open(filename, "w")
    f.write("<?xml version='1.0' encoding='UTF-8'?>\n")
    f.write("<osm version='0.6' generator='JOSM'>\n")

    ways = {}
    nodes_for_export = {}
    next_node_id = 0
    next_way_id = 0
    
    edges_tested = set()
    edges_by_mass = list(map.edges)
    edges_by_mass.sort(key=lambda x: -x.w)
    for e in edges_by_mass:
        if e in edges_tested: continue
        seg = e.get_segment()
        edges_tested.update(set(seg))
        #seg = map.build_longer_segment(seg,edges_tested)
        
        l = sum([e.len for e in seg])
        ladj = sum([e.mass for e in seg])
                
        if True or l > 300 or ladj/l > 2.0: 
            newway=[seg[0].node1]+[e.node2 for e in seg]
            for n in newway:
                if n not in nodes_for_export:
                    next_node_id+= 1
                    nodes_for_export[n]=next_node_id
            next_way_id += 1
            ways[next_way_id] = (ladj/l,newway)
            
    #print nodes_export
    for n,id in nodes_for_export.iteritems():
        lat, lon = latlon_from_xy(n.x,n.y)
        f.write("<node id='-%s' visible='true' lat='%f' lon='%f' />\n" % (id, lat,lon))
    for way_id, waymap in ways.iteritems():
        avg_weight, nlist = waymap
        f.write("<way id='-%s' action='modify' visible='true'>\n" % (way_id,))
        for n in nlist:
            f.write("  <nd ref='-%s' />\n" % (nodes_for_export[n],))
        f.write("<tag k='highway' v='road' />\n")
        if DEBUG: f.write("<tag k='weight' v='%s' />\n" % avg_weight)
        f.write("</way>\n")
    f.write("</osm>")
    print 'OK. ways=', len(ways), ' nodes=', len(nodes_for_export)
    print 'left = %s %s' % (len(map.nodes),len(map.edges))

# ======================= PROCESSING ===============================
def C_from_AB(AB,CA,CB):
    p = (CA + CB + AB)/2
    if (p - AB)<0.01: return 0.0
    if (p - CA)<0.01: return 0.0
    if (p - CB)<0.01: return 0.0
    area = (p * (p-AB) * (p-CA) * (p-CB)) ** 0.5
    return area/AB * 2


def simplify(radius):
    # remove straight sections of edges
        
    if DEBUG: print 'SIMPLIFY...edges=%s' % (len(map.edges),),
    log = collections.defaultdict(int)

    for C in list(map.nodes):
        if len(C.edges)!=2:
            log['len_not_2']+=1 
            continue
        
        e1,e2 = list(C.edges)
        if e1.node1==C: A = e1.node2
        else: A = e1.node1
        if e2.node1==C: B = e2.node2
        else: B = e2.node1
        
        if A==B: 
            e1.kill()
            e2.kill()
            log['a=b']+=1
            continue

        AB = A-B
        
        if AB<radius:
            e1.kill()
            e2.kill()
            A.merge(B)
            log['sharp']+=1
            continue

        CA = C-A
        CB = C-B
        
        if CA>AB and C_from_AB(CA,CB,AB)<radius:
            # C is very sharp angle (suspect noise)
            new_edge = map.find_or_create_edge(A,B)
            if e1.node2 == A: e1.flip()
            new_edge.add_mass(e1)
            e1.kill()
            e2.kill()
            log['sharpC']
            continue
        if CB>AB and C_from_AB(CB,CA,AB)<radius:
            # C is very sharp angle (suspect noise)
            new_edge = map.find_or_create_edge(A,B)
            if e2.node1 == B: e2.flip()
            new_edge.add_mass(e2)
            e1.kill()
            e2.kill()
            log['sharpC']
            continue
        
        if CA < AB and CB < AB and C_from_AB(AB, CA, CB)<radius:
            C.move_to_edge(A,B)
            new_edge = map.find_or_create_edge(A,B)
            if e1.node2==A: e1.flip()
            if e2.node1==B: e2.flip()
            new_edge.add_mass(e1)
            new_edge.add_mass(e2)
            e1.kill()
            e2.kill()
            log['flat']+=1
            continue    
        
        log['OK']+=1
    if DEBUG: print '   ... edges_after=%s' % (len(map.edges),), ' log=',log


def zip_from_node(C,radius):
    # tests if any exit edge combinations can be zip-merged (are running close enough)
    if C not in map.nodes: return
    ledges = list(C.edges)
    for e1_idx in range(len(ledges)-1):
        for e2_idx in range(e1_idx+1,len(ledges)):
            e1 = ledges[e1_idx]
            e2 = ledges[e2_idx]
            if zip_v(C,e1,e2,radius): return
            
    
def zip_v(A, edge1,edge2,radius):
    #zip two edges that form V shape, if possible. 
    # return True if success, False if not
    # edges can be any direction (will flip if needed)
    # A is matching node for both e1,e2
    
    # cross check data validity
    if A != edge1.node1 and A != edge1.node2: raise Exception, 'wrong zip_v: no A'
    if A != edge2.node1 and A != edge2.node2: raise Exception, 'wrong zip_v: no A'
    if edge1==edge2: raise Exception, 'wrong zip_v: sames edges called'
    
    
    # if edge is shorter than radius - compress it and check-zip from new node
    if edge1.len<radius:
        zip_from_node( edge1.node1.merge(edge1.node2) ,radius)
        return True
    if edge2.len<radius: 
        zip_from_node( edge2.node1.merge(edge2.node2),radius)
        return True
    
    # if edges are the same - join into one direction
    if edge1.node1 == edge2.node2 and edge1.node2 == edge2.node1:
        # case 1 - edges 
        #sys.stdout.write('f')
        #sys.stdout.flush()
        edge2.flip()
        edge1.add_mass(edge2)
        edge2.kill()
        zip_from_node(edge1.node1,radius)
        zip_from_node(edge1.node2,radius)
        return True
    
    # for convenience - e1 is always shorter than e2.
    if edge1.len>edge2.len: 
        e1, e2 = edge2, edge1 
    else:
        e1, e2 = edge1, edge2
        
    # node C is the "other" node of shorter edge (it will be zipped into e2 if appropriate
    if e1.node1 == A: C = e1.node2
    else: C = e1.node1
    # node B is the "other" node of longer edge.
    if e2.node1 == A: B = e2.node2
    else: B = e2.node1

    CB = B-C
    
    if CB < radius:
        C.merge(B)
        zip_from_node(C,radius)
        zip_from_node(A,radius)
        return True
    if CB > e2.len: return False
    # does it have merge potential?
    if C_from_AB(e2.len,e1.len,CB) > radius: return False 
    
    # zip !!!
    C.move_to_edge(A,B)
    e2.split(C)
    
    zip_from_node(C, radius)
    zip_from_node(A, radius)
    return True


def merge_edges3(radius):
    # note - allow redirect edge if needed.
    if DEBUG: print 'MERGING EDGES3... edges=%s' % (len(map.edges),),

    log = collections.defaultdict(int)
            
    edges_tested = set()
    
    for bin in map.grid.values():
        #print 'check bin', len(bin)
        log['bins_tested']+=1
        if len(bin)>1: 
            nlist = list(bin)
            for Cidx in range(len(nlist)-1):
                C = nlist[Cidx]
                C_endpoints = C.nodes_within(CHKDIST)
                
                #log['nodes_tested']+=1
                for Aidx in range(Cidx+1,len(nlist)):
                    A=nlist[Aidx]
                    #log['pair_tested']+=1
                
                    if A not in bin: continue
                    if C-A > radius: continue
                    #log['pair_close']+=1
                    A_endpoints = A.nodes_within(CHKDIST)
                    if endpoints_match(C_endpoints, A_endpoints):
                        #log['pair_match']+=1
                        C.merge(A)
                        zip_from_node(C, radius)
                        C_endpoints = C.nodes_within(CHKDIST)
        # option two - check all edges from here
        edges_todo = set()
        for n in bin: edges_todo.update(n.edges)
        edges_todo.difference_update(edges_tested)
        edges_tested.update(edges_todo)
        
        while edges_todo:
            edge = edges_todo.pop()
            if edge not in map.edges: continue
            edge_n1_endpoints = edge.node1.nodes_within(CHKDIST,set([edge]))
            edge_n2_endpoints = edge.node2.nodes_within(CHKDIST,set([edge]))
            
            log['edges_tested']+=1
            
            nlist = map.nodes_around_edge2(edge,radius)
            # zipper.
            for C in nlist:
                C_n1_endpoints = C.nodes_within(CHKDIST+ (C-edge.node1))
                C_n2_endpoints = C.nodes_within(CHKDIST+ (C-edge.node2))
                
                log['e-n_count']+=1
                
                if endpoints_match(edge_n1_endpoints,C_n1_endpoints) or \
                    endpoints_match(edge_n2_endpoints,C_n2_endpoints):

                    log['e-n_match']+=1
                    
                    C.move_to_edge(edge.node1,edge.node2)
                    edge.split(C)
                    #sys.stdout.write('zip!')
                    #sys.stdout.flush()
                    zip_from_node(C, radius)
                    break

                
    if DEBUG: print '... edges_after=%s log=%s'% (len(map.edges),log)
    
def endpoints_match(ep1, ep2):
    # two collections of endpoints - do they have any points close
    #return True
    for p1 in ep1:
        for p2 in ep2:
            if p1-p2<20.0: return True
    return False    

def zip_nodes_all(radius):
    if DEBUG: print 'ZIP nodes all', len(map.edges), '...',
    for n in list(map.nodes):
        if n not in map.nodes: continue
        zip_from_node(n,radius)
    if DEBUG: print 'after:',len(map.edges)
    simplify(radius/3)
            
def import_all(wildcard=FILEMASK):
    cnt=0    
    print 'IMPORT from path=', wildcard
    for f in glob.glob(wildcard): 
        if f[-4:] != '.gpx': continue
        cnt+=1
        #if cnt>20: break
        import_file(f)
    print 'IMPORT done for %s files' % cnt

def test():
    log = collections.defaultdict(int)
    for node in map.nodes:
        ep = set()
        node.nodes_within(10.0,ep)
        log['nodes']+=1
        if len(ep)<1:
            log['nodes_wo_end'] += 1
            for e in node.edges:
                if e.len>10.0:
                    node.nodes_within(10.0,ep)
        log['nodes'+str(len(node.edges))] += 1
                
            
    print log


def process():
    simplify(3.0)
    merge_edges3(3.0)
    zip_nodes_all(10.0)

    merge_edges3(5.0)
    zip_nodes_all(10.0)
    map.remove_untraveled_edges(1.6)
    merge_edges3(5.0)
    zip_nodes_all(15.0)
    return

def print_map():
    s = sum([e.len for e in map.edges])
    so = sum([e.mass for e in map.edges])
    print 'map: e=%s n=%s len=%s mass=%s' % (len(map.edges),len(map.nodes),s,so)
    
# ======= TEST AREA ============

FILEMASK = 'test3.gpx'
def main():
    global FILEMASK
    global OUTFILE
    parser = optparse.OptionParser()
    parser.add_option("--in", dest="FILEMASK",
                  help='File or mask for gpx files (ex: ../files/*.gpx)', metavar="FILEMASK",
                  default=FILEMASK)
    parser.add_option("--out", dest="OUTFILE",
                  help='File for output (default: %s)' % OUTFILE, metavar="OUTFILE",
                  default=OUTFILE)
    options = parser.parse_args()[0]
    if options.FILEMASK: FILEMASK = options.FILEMASK
    if options.OUTFILE: OUTFILE = options.OUTFILE
    parser.print_help()
    print
    t=  time.time()
    print ' starting ', time.strftime("%Y.%m.%d %H:%M:%S",time.localtime(t))
    import_all(FILEMASK)
    process()
    export_to_osm(OUTFILE)
    print ' ending', time.strftime("%Y.%m.%d %H:%M:%S",time.localtime(time.time())), ' elapsed ', time.time()-t
    print 

if __name__ == '__main__':
    main()
    
