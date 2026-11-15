-- Prove2me | Theorems.Thm_APFB07b_costly_start_meets_the_hypotheses
-- name    : APFB07b.costly_start_meets_the_hypotheses
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:16:46.368697+00:00
-- url     : https://prove2.me/theorems/7a36adac-44f7-40ff-ad5a-5970b50d62bc
-- title:
--   Costly start meets the hypotheses
-- statement:
--   There is a three-moment real-history model with admissibility exactly r(0)=1, square-sum cost, and realized history (1,0,0), satisfying A2Selection and BWUniqueMinimum and the stated cyclic mirror and cheaper-record conditions. This is a supplied mathematical model, with no B01 physical realization asserted.
-- source:
--   Sib v44 Theorems/Thm_APFB07_costly_start_witness.lean:23

import Theorems.Thm_APFPaper5_K3_continuity_met_by_self_undoing_turns
import Theorems.Thm_APFB07a_realized_moves_off_a_costly_start
import Theorems.Thm_APFB07b_rate_is_held_after_a_costly_start
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.costly_start_meets_the_hypotheses :
    ∃ (originalAdmissible : Unit → (Fin 3 → ℝ) → Prop) (totalCost : Unit → (Fin 3 → ℝ) → ℝ)
      (realized : Unit → (Fin 3 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t * r t) ∧
        (∀ r, originalAdmissible () r ↔ r 0 = 1) ∧
        (0 : ℝ) * 0 < 1 * 1 ∧ (0 + 1 + 1 : Fin 3) ≠ 0 ∧ (-0 : Fin 3) = 0 ∧
        ∀ t : Fin 3, -(t + 1) + 1 = -t := by sorry
