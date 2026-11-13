-- Prove2me | Theorems.Thm_DirKECC1549_Main_induced_walk_project
-- name    : DirKECC1549.Main.induced_walk_project
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T09:47:53.855999+00:00
-- url     : https://prove2.me/theorems/27060899-31d5-4a61-8d02-1bf16cf67d37
-- title:
--   Projecting an induced-subgraph walk to the original graph
-- statement:
--   Let $G$ be a finite directed multigraph and let $x,y$ belong to a vertex set $S$. Every directed walk from $x$ to $y$ in the induced graph $G[S]$ maps to a directed walk from $x$ to $y$ in $G$ by replacing each induced edge identifier by its original edge identifier. This projects walks while retaining edge identities, including parallel edges and loops.
-- source:
--   Derived auxiliary walk transport lemma for Claim 1, Georgiadis et al., STOC 2027 submission #1549, Section 3.3, p.17.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main
theorem induced_walk_project {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S)
    (q : List (Fin (inducedEdges G S).card))
    (hq : IsWalk (induced G S) (posIn S x hx) q (posIn S y hy)) :
    IsWalk G x (q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1)) y := by sorry
end DirKECC1549.Main
