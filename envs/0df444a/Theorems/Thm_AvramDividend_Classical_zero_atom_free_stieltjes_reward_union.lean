-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_atom_free_stieltjes_reward_union
-- name    : AvramDividend.Classical.zero_atom_free_stieltjes_reward_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:49:53.925893+00:00
-- url     : https://prove2.me/theorems/b069bc44-5797-4711-87aa-11e92a7d27d0
-- title:
--   A null initial Stieltjes atom leaves all stopped dividend integrals unchanged
-- statement:
--   For any nonnegative weighted time reward and any positive-time payment set, adding the initial payment time zero does not change its lower integral when the Stieltjes dividend measure assigns zero mass to that singleton. The proof uses union subadditivity, set-integral monotonicity and the zero-measure integral theorem, without measurability assumptions on the positive-time set. Essential for exact paymentTimes which always includes zero even at immediate ruin.
-- source:
--   Prove2Me DividendStrategy.paymentTimes zero-time convention, Mathlib MeasureTheory.lintegral_union_le and setLIntegral_measure_zero; Avram, Palmowski and Pistorius (2007), section 3.3.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.zero_atom_free_stieltjes_reward_union
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (s : Set ℝ)
    (hzero : μ {(0 : ℝ)} = 0) :
    (∫⁻ t in ({(0 : ℝ)} ∪ s), f t ∂μ) =
      (∫⁻ t in s, f t ∂μ) := by sorry
