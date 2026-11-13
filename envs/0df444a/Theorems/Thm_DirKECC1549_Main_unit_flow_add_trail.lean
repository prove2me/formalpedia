-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_add_trail
-- name    : DirKECC1549.Main.unit_flow_add_trail
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:45:32.91175+00:00
-- url     : https://prove2.me/theorems/e567c2a9-36a4-4543-aca6-0d0239b64312
-- title:
--   Adding a disjoint directed trail to a unit flow
-- statement:
--   Let $D$ be a finite directed multigraph, let $F$ support an integral unit-capacity flow of value $q$ from $u$ to $v$, and let $p$ be a directed $u$–$v$ trail whose edge set is disjoint from $F$. Then the union of $F$ with the edges of $p$ supports an integral unit-capacity $u$–$v$ flow of value $q+1$.
--
--   This conservation lemma constructs the flow of a disjoint family one trail at a time. Edge identifiers distinguish parallel edges, loops are allowed, and the statement includes coincident endpoints.
-- source:
--   Derived conservation step for flow decomposition; Ahuja, Magnanti and Orlin, Network Flows (1993), Section 3.5; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9, for the mission graph encoding.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_add_trail {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m)) (p : List (Fin m))
    (hF : IsUnitFlow D F u v q) (hp : IsTrail D u p v)
    (hdis : Disjoint F p.toFinset) : IsUnitFlow D (F ∪ p.toFinset) u v (q + 1) := by sorry
end DirKECC1549.Main
