-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_sec5_2_fact_2
-- name    : DirKECC1549.Main.Supplement.sec5_2_fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:19:04.529925+00:00
-- url     : https://prove2.me/theorems/b6f89593-666b-4dbd-81e4-e4c96424ee0e
-- title:
--   Section 5.2, fact 2 — separators in G are exactly split-edge cuts in G′_C
-- statement:
--   Let $G$ be a directed multigraph, $k\ge1$, $C\subseteq V(G)$, and $G'_C$ the partially vertex-split graph with bundles of $k$ parallel edges. Let $x,y\in C$ be distinct and $X\subseteq V\setminus C$. Then
--   $$X\ \text{is an $(x,y)$-separator in }G\iff\{(v^-,v^+):v\in X\}\ \text{is an $(x,y)$-edge cut in }G'_C,$$
--   where an $(x,y)$-separator is a set $X\not\ni x,y$ such that $G-X$ has no directed path from $x$ to $y$, and an $(x,y)$-edge cut is a set of edges whose deletion leaves no directed path from $x$ to $y$.
--
--   This is the "false" direction of the paper's vertex-connectivity reduction: a small vertex separator whose vertices are all split becomes a small edge cut.
--
--   **Formalization Note** The split edge of $v$ is the edge id $km+v$; $x,y\in C$ are the vertices $x,y$ of $G'_C$. $k\ge1$ is the paper's standing assumption; at $k=0$ the split graph would have no copies of the original edges.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and lies on no useful path, so it changes no edge or vertex connectivity; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention of the published Graph definition; parallel edges are distinct ids; same instances
--   - encoding: G′_C with at most 2n vertices and km + n edges → vertex set Fin (2n), edge ids Fin (k·m + n), with an unused vertex n + v carrying a self-loop for each v ∈ C; reason: the unused vertices and loops lie on no path between other vertices; the set of split edges of X is unchanged
--   - encoding: for x, y ∈ C (the separator notion of §5.1 is for distinct s, t) → hypothesis x ≠ y; reason: §5.1 defines (s, t)-separators only for distinct s, t
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 5.2, fact 2, p.26 (separators §5.1 p.25; G′_C p.25)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_VertexConn

set_option autoImplicit false

namespace DirKECC1549.Main.Supplement

open DirKECC1549.Main

/-- Section 5.2, fact 2, p.26: for distinct `x, y ∈ C` and `X ⊆ V \ C`, `X` is an
`(x, y)`-separator in `G` if and only if its split edges `{(v⁻, v⁺) : v ∈ X}` form an
`(x, y)`-edge cut in `G′_C`. -/
theorem sec5_2_fact_2 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (G : Fin m → Fin n × Fin n)
    (C X : Finset (Fin n)) (hX : Disjoint X C) (x y : Fin n) (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x ≠ y) :
    IsSeparator G X x y ↔
      IsEdgeCut (splitGraph k G C) (X.image (splitEdge k m)) (entryV x) (entryV y) := by sorry

end DirKECC1549.Main.Supplement
