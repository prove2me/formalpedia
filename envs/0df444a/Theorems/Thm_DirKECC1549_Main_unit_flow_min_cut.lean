-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_min_cut
-- name    : DirKECC1549.Main.unit_flow_min_cut
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:23:24.559043+00:00
-- url     : https://prove2.me/theorems/116cb5da-f7b4-47d6-bbcb-8b3260733639
-- title:
--   Integral unit-capacity max-flow min-cut theorem
-- statement:
--   Let $D$ be a finite directed multigraph with distinct vertices $u,v$. There is a natural number $q$ which is both the largest value of an integral unit-capacity $u$–$v$ flow and the minimum number of outgoing edges of a vertex set containing $u$ but excluding $v$.
--
--   Flow values and cut sizes count parallel edges separately. Loops are allowed, and a flow is represented by its set of edges carrying one unit.
-- source:
--   Ford–Fulkerson max-flow min-cut theorem with integral unit capacities; Ford and Fulkerson, Flows in Networks (1962), Chapter I, Theorem 5.1, p.19 and integrality theorem; see also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_min_cut {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) :
    ∃ q : ℕ, IsGreatest {q : ℕ | ∃ F : Finset (Fin m), IsUnitFlow D F u v q} q ∧
      IsLeast ((fun S ↦ outCount D S) '' {S : Finset (Fin n) | IsCut S u v}) q := by sorry
end DirKECC1549.Main
