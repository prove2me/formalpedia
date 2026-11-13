-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_toggle_residual_trail
-- name    : DirKECC1549.Main.unit_flow_toggle_residual_trail
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T11:17:41.841012+00:00
-- url     : https://prove2.me/theorems/fc993808-ed6f-4568-86de-7cd1c4d300e7
-- title:
--   Toggling a residual trail augments an integral unit flow
-- statement:
--   Let $D$ be a finite directed multigraph, let $F$ support an integral unit-capacity flow of value $q$ from $u$ to $v$, and let $p$ be a directed $u$–$v$ trail in the residual graph obtained by reversing the edges of $F$. Then the symmetric difference
--
--   $$F\mathbin{\triangle}E(p)$$
--
--   supports an integral unit-capacity $u$–$v$ flow of value $q+1$. The result also covers coincident endpoints: then both flow-balance equations have zero net source contribution. Parallel edges have distinct identifiers, and loops are allowed.
-- source:
--   Ford–Fulkerson, Flows in Networks (1962), Chapter I, Section 5, augmentation along a residual path, p.19; generalized to residual trails for the mission unit-flow encoding, Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_toggle_residual_trail {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) (p : List (Fin m))
    (hp : IsTrail (flipEdges D F) u p v) :
    IsUnitFlow D ((F \ p.toFinset) ∪ (p.toFinset \ F)) u v (q + 1) := by sorry
end DirKECC1549.Main
