-- Prove2me | Theorems.Thm_APFB07b_pinned_loop_meets_the_hypotheses
-- name    : APFB07b.pinned_loop_meets_the_hypotheses
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:13:41.238174+00:00
-- url     : https://prove2.me/theorems/dd123df3-1d34-4c03-a7d6-a662b758fa68
-- title:
--   Pinned loop meets the hypotheses
-- statement:
--   There is a four-moment model of A2Selection and BWUniqueMinimum with square-sum price, a mirror-closed admissible set pinned to 1 at moment 0 and -1 at moment 2, and realized history (1,0,-1,0). Its realized record differs after two cyclic steps. No physical occupied loop is constructed.
-- source:
--   Sib v44 Theorems/Thm_APFB07_pinned_loop_witness.lean:23

import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.pinned_loop_meets_the_hypotheses :
    ∃ (originalAdmissible : Unit → (Fin 4 → ℝ) → Prop) (totalCost : Unit → (Fin 4 → ℝ) → ℝ)
      (realized : Unit → (Fin 4 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t * r t) ∧
        (∀ r, originalAdmissible () r → originalAdmissible () (fun t => r (-t))) ∧
        realized () (0 + 1 + 1) ≠ realized () 0 := by sorry
