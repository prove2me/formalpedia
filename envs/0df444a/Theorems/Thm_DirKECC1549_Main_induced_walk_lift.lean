-- Prove2me | Theorems.Thm_DirKECC1549_Main_induced_walk_lift
-- name    : DirKECC1549.Main.induced_walk_lift
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T09:48:29.402768+00:00
-- url     : https://prove2.me/theorems/fe8fc7c8-71c0-4dbf-8ff1-99c30001b086
-- title:
--   Lifting a walk to an induced subgraph
-- statement:
--   Let $G$ be a finite directed multigraph and let $x,y$ belong to a vertex set $S$. Every directed walk from $x$ to $y$ whose edges have both endpoints in $S$ corresponds to a walk in the induced graph $G[S]$, with the same original edge identities after undoing the edge renumbering. This lifts individual walks to an induced subgraph, including parallel edges and loops.
-- source:
--   Derived auxiliary walk transport lemma for Claim 1, Georgiadis et al., STOC 2027 submission #1549, Section 3.3, p.17.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main
theorem induced_walk_lift {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S)
    (p : List (Fin m)) (hp : IsWalk G x p y)
    (he : ∀ e ∈ p, (G e).1 ∈ S ∧ (G e).2 ∈ S) :
    ∃ q : List (Fin (inducedEdges G S).card),
      q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1) = p ∧
      IsWalk (induced G S) (posIn S x hx) q (posIn S y hy) := by sorry
end DirKECC1549.Main
