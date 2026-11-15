-- Prove2me | Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
-- name    : APFB07b.realized_history_retraces_of_sum_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:10:28.356982+00:00
-- url     : https://prove2.me/theorems/6dbc4e91-8b8f-4aaf-93c2-8d87a0e9c7db
-- title:
--   Realized history retraces of sum cost
-- statement:
--   Assume A2Selection and BWUniqueMinimum on finite record histories. If total cost is a sum of record costs and composing any admissible history with a supplied moment permutation remains admissible, the realized history is fixed by that permutation. The permutation need not be a physical reversal unless separately bound as one.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_history_retraces.lean:70

import Theorems.Thm_APFB07b_realized_fixed_by_cost_symmetry
import Theorems.Thm_APFB07b_realized_has_no_rate_of_present_records
import Theorems.Thm_APFB07b_realized_rate_not_forbidden
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB07b.realized_history_retraces_of_sum_cost {Interface : Type*} {T : Type*} [Fintype T]
    {R : Type*} (originalAdmissible : Interface → (T → R) → Prop)
    (totalCost : Interface → (T → R) → ℝ) (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (hundo : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (sigma t)))
    (i : Interface) (t : T) : realized i (sigma t) = realized i t := by sorry
