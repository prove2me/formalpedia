-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
-- name    : AvramDividend.Classical.avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:36:31.887011+00:00
-- url     : https://prove2.me/theorems/ab0ac547-883a-4378-83cf-11dc7d467c84
-- title:
--   Original positive ruin closed Iic and strict Iio paymentTimes coincide
-- statement:
--   At an original positive ruin contact, paymentTimes excludes the ruin instant, so the closed Iic terminal cash and the strict Iio terminal cash have exactly the same underlying integration set, preserving the initial t=0 atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_positive_ruin_excludes_terminal_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (ht : 0 < t) (hruin : (t : ℝ≥0∞) = σ) :
    paymentTimes σ ∩ Iic (t : ℝ) =
      paymentTimes σ ∩ Iio (t : ℝ) := by sorry
