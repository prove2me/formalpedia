-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_sec5_2_fact_1
-- name    : DirKECC1549.Main.Supplement.sec5_2_fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:18:38.785768+00:00
-- url     : https://prove2.me/theorems/4f61c83a-8729-4e77-928a-f90a3d9ea3ed
-- title:
--   Section 5.2, fact 1 — k-vertex-connected in G implies k-edge-connected in G′_C
-- statement:
--   Let $G$ be a directed multigraph, $k\ge1$, $C\subseteq V(G)$, and let $G'_C$ be the partially vertex-split graph in which every vertex outside $C$ is split into $v^-,v^+$ joined by the split edge $(v^-,v^+)$ and every edge of $G$ is replaced by a bundle of $k$ parallel edges from the exit copy of its tail to the entry copy of its head. For $x,y\in C$:
--   $$x,y\ \text{$k$-vertex-connected in }G\ \Longrightarrow\ x,y\ \text{$k$-edge-connected in }G'_C.$$
--
--   This is the "true" direction of the paper's vertex-connectivity reduction: a $k$-vertex-connected pair is never separated by an edge-connectivity computation on a split graph that keeps both endpoints unsplit.
--
--   **Formalization Note** $x,y\in C$ are unsplit, so they are the vertices $x,y$ of $G'_C$. $k$-edge-connectivity is the published definition ($x=y$, or $k$ edge-disjoint paths in each direction).
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and lies on no useful path, so it changes no edge or vertex connectivity; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention of the published Graph definition; parallel edges are distinct ids; same instances
--   - encoding: G′_C with at most 2n vertices and km + n edges → vertex set Fin (2n), edge ids Fin (k·m + n), with an unused vertex n + v carrying a self-loop for each v ∈ C; reason: the unused vertices and loops lie on no path between other vertices, so no edge-connectivity between vertices of C changes
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 5.2, fact 1, p.26 (G′_C defined on p.25)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_VertexConn

set_option autoImplicit false

namespace DirKECC1549.Main.Supplement

open DirKECC1549.Main

/-- Section 5.2, fact 1, p.26: for `x, y ∈ C`, if `x, y` are `k`-vertex-connected in `G`, then they
are `k`-edge-connected in the partially vertex-split graph `G′_C` (bundles of `k` parallel edges). -/
theorem sec5_2_fact_1 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (G : Fin m → Fin n × Fin n)
    (C : Finset (Fin n)) (x y : Fin n) (hx : x ∈ C) (hy : y ∈ C)
    (hxy : KVertexConnected k G x y) :
    KEdgeConnected k (splitGraph k G C) (entryV x) (entryV y) := by sorry

end DirKECC1549.Main.Supplement
