-- Prove2me | Theorems.Thm_DirKECC1549_Main_induced_disjoint_paths
-- name    : DirKECC1549.Main.induced_disjoint_paths
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T09:34:09.715013+00:00
-- url     : https://prove2.me/theorems/caa12acc-7439-4089-b096-e7eda1bf51a0
-- title:
--   Disjoint trails in a walk-convex induced subgraph
-- statement:
--   Let $G$ be a finite directed multigraph, let $S$ be a vertex set containing $x$ and $y$, and assume that every edge of every directed walk from $x$ to $y$ has both endpoints in $S$. For each $k\ge 0$,
--
--   $$G\text{ has $k$ pairwise edge-disjoint directed trails from $x$ to $y$}\iff G[S]\text{ has $k$ such trails}.$$
--
--   This transfers directional edge-connectivity to an induced subgraph. Parallel edges have distinct identities, and loops are permitted. The formal induced graph renumbers its vertices and edges.
-- source:
--   Auxiliary lemma for Claim 1, Georgiadis, Kipouridis, Kosinas, Papadopoulos, Pergaminelis, STOC 2027 submission #1549, Section 3.3, p.17; derived supporting graph-theoretic statement.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main
theorem induced_disjoint_paths {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (k : ℕ) (hx : x ∈ S) (hy : y ∈ S)
    (hwalk : ∀ p, IsWalk G x p y → ∀ e ∈ p, (G e).1 ∈ S ∧ (G e).2 ∈ S) :
    HasDisjointPaths G k x y ↔
      liftRel S (HasDisjointPaths (induced G S) k) x y := by sorry
end DirKECC1549.Main
