-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:37:57.409573+00:00
-- url     : https://prove2.me/theorems/290e0cc2-2f83-41d3-82d8-b54d0b5eda9a
-- title:
--   Original Cash payment-time discount bounded by one at nonnegative times
-- statement:
--   For nonnegative q and a nonnegative original payment time, the exact source Cash integrand's discount selector has ENNReal value at most one, including its zero branch. This discharges the pointwise coefficient hypothesis of the finite weighted Cash atom tsum comparison at effective nonnegative source times.
-- source:
--   Source paymentTimes/ruinTime definitions in AvramDividend.Classical DividendStrategy and pinned Mathlib Real.exp_le_one_iff, ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
    (ρ : ℝ≥0∞) (q s : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (if s ∈ paymentTimes ρ then
        ENNReal.ofReal (Real.exp (-(q * s))) else 0) ≤ 1 := by sorry
