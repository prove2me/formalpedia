-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_extract_trail
-- name    : DirKECC1549.Main.unit_flow_extract_trail
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:30:46.602205+00:00
-- url     : https://prove2.me/theorems/556d88aa-b7aa-4f12-81aa-7e0b8fcf24bb
-- title:
--   Extracting a trail from a positive integral unit flow
-- statement:
--   Let $D$ be a finite directed multigraph, let $u\ne v$, and let $F$ be the support of an integral unit-capacity $u$–$v$ flow of value $q+1$. There is a directed $u$–$v$ trail $p$ using only edges of $F$ such that deleting the edges of $p$ from $F$ leaves the support of a unit-capacity $u$–$v$ flow of value $q$.
--
--   This is the one-trail extraction step in the integral flow decomposition theorem. Parallel edges are distinguished by their identifiers, and loops are allowed.
-- source:
--   Derived elementary step of integral flow decomposition, Ahuja, Magnanti and Orlin, Network Flows (1993), Section 3.5; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9, in the mission multigraph encoding.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_extract_trail {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v (q + 1)) :
    ∃ p : List (Fin m), IsTrail D u p v ∧ p.toFinset ⊆ F ∧
      IsUnitFlow D (F \ p.toFinset) u v q := by sorry
end DirKECC1549.Main
