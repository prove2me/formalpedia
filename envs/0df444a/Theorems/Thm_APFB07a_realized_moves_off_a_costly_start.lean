-- Prove2me | Theorems.Thm_APFB07a_realized_moves_off_a_costly_start
-- name    : APFB07a.realized_moves_off_a_costly_start
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:13:03.352806+00:00
-- url     : https://prove2.me/theorems/c8b5ba79-3aba-46fa-a9ce-be075e081170
-- title:
--   Realized moves off a costly start
-- statement:
--   For finite histories, assume A2Selection, total cost equal to a sum of point costs, and admissibility exactly pinning one marked moment to e. If a record cheaper than e exists, the realized history equals e at the marked moment and has strictly cheaper records at every other moment. The domain and sum-price binding are supplied.
-- source:
--   Sib v44 Theorems/Thm_APFB07_moves.lean:78

import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB07a.realized_moves_off_a_costly_start {Interface : Type*} {T : Type*} [Fintype T]
    [DecidableEq T] {R : Type*} (originalAdmissible : Interface → (T → R) → Prop)
    (totalCost : Interface → (T → R) → ℝ) (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (t0 : Interface → T) (e : Interface → R)
    (hadm : ∀ i r, originalAdmissible i r ↔ r (t0 i) = e i)
    (i : Interface) (v : R) (hv : c i v < c i (e i)) (t : T) (ht : t ≠ t0 i) :
    realized i (t0 i) = e i ∧ c i (realized i t) < c i (e i) := by sorry
