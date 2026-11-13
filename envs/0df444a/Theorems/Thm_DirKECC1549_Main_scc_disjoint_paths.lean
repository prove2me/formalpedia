-- Prove2me | Theorems.Thm_DirKECC1549_Main_scc_disjoint_paths
-- name    : DirKECC1549.Main.scc_disjoint_paths
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T05:11:04.916508+00:00
-- url     : https://prove2.me/theorems/253a1eea-5eba-4711-857d-df7583744af8
-- title:
--   Disjoint directed trails are preserved by restriction to a strongly connected component
-- statement:
--   Let $G$ be a finite directed multigraph and let $S$ be the strongly connected component of a vertex $a$. If $x,y\in S$ and $k\ge 0$, then
--
--   $$
--   \text{there are $k$ pairwise edge-disjoint $x$–$y$ directed trails in $G$}
--   \quad\Longleftrightarrow\quad
--   \text{there are $k$ such trails in $G[S]$}.
--   $$
--
--   This directional preservation result supports reductions of edge-connectivity questions to strongly connected components. Parallel edges retain their identities and loops are allowed.
--
--   **Formalization Note** The induced graph renumbers vertices and edges; the relation on its vertices is transported back to $G$.
-- source:
--   Auxiliary directional trail-transport lemma for Claim 1, Section 3.3, p.17, Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026). The statement is a generalization of the path-preservation step implicit in that claim.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main
 theorem scc_disjoint_paths {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (a x y : Fin n) (k : ℕ) (hx : StronglyConn G a x) (hy : StronglyConn G a y) :
    HasDisjointPaths G k x y ↔
      liftRel (sccOf G a) (HasDisjointPaths (induced G (sccOf G a)) k) x y := by sorry
end DirKECC1549.Main
