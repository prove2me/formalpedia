-- Prove2me | Theorems.Thm_AvramDividend_Classical_strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
-- name    : AvramDividend.Classical.strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:18:40.688276+00:00
-- url     : https://prove2.me/theorems/7a9793f9-3738-4afa-a268-0afbc9fa4d00
-- title:
--   Strict lower-crossing clock cannot touch its boundary under a positive right germ
-- statement:
--   For a real-valued path on nonnegative time, if its strict lower-crossing clock of a boundary is finite and equals time τ and there is a strictly positive interval immediately after τ on which the path stays at or above the boundary, then the path cannot equal the boundary at τ. This pathwise bridge isolates the deterministic infimum-of-strict-crossings step in the BV no-downward-creeping argument; the remaining stochastic task is to establish a positive right germ at the stopping time.
-- source:
--   Proof checkpoint for AvramDividend.Classical.bv_strict_lower_exit_no_creeping_ae UUID 43a28d8e-14f3-44d6-8b46-347138818c52 and stopped-scale target 09caed2c-1cc0-4083-8a24-a39b70d511c8, using exact strict lower first-passage infimum.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
    (f : ℝ≥0 → ℝ) (b : ℝ) (τ : ℝ≥0)
    (hτ : (τ : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : f t < b), (t : ℝ≥0∞)))
    (hRight : ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, τ < t → t < τ + ε → b ≤ f t) :
    f τ ≠ b := by sorry
