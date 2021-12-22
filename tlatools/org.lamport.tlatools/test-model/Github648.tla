--------------------- MODULE Github648 -----------------------------
EXTENDS TLC, Naturals


DirectedGraphs(nodes) ==
    [edge : SUBSET (nodes \X nodes)]

TestGraph ==
    \* The definition of TestGraph is evaluated multiple times.  If the def.
    \* involves TLC!RandomElement or Randomization!* the invariant Inv below
    \* will be violated.
    RandomElement(DirectedGraphs(1..3))
    \* CHOOSE g \in DirectedGraphs(1..3): g.edge = {}

-----------------------------------------------------------------------------
CONSTANT Graph

VARIABLE v, w
vars == <<v, w>>

Init ==
    /\ v \in Graph.edge
    /\ w \in Graph.edge

Next ==
    UNCHANGED vars

Inv ==
    /\ v \in Graph.edge
    /\ w \in Graph.edge

=============================================================================
