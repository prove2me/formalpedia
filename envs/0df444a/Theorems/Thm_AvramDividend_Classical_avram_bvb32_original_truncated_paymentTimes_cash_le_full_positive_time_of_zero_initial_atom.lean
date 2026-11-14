-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_truncated_paymentTimes_cash_le_full_positive_time_of_zero_initial_atom
-- name    : AvramDividend.Classical.avram_bvb32_original_truncated_paymentTimes_cash_le_full_positive_time_of_zero_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:25:30.605797+00:00
-- url     : https://prove2.me/theorems/2c4d8763-0b7b-41a2-8771-d81cb16900d9
-- title:
--   Exact original paymentTimes clipped dividend Stieltjes cash is bounded by full positive physical-time cash when initial dividend atom vanishes
-- statement:
--   The original cumulative dividend paymentTimes(ruin) includes time zero, and the original uniform clipped grid F_n integrates over paymentTimes intersect Iio(b). For any actual Stieltjes dividend measure whose singleton zero atom is exactly zero, the clipped paymentTimes integral of every nonnegative reward f is bounded by its full positive physical-time Ioc(0,T) integral whenever b≤T. This explicitly accounts for the original time-zero atom rather than deleting it by assumption. It is the exact measure-monotonicity step needed for the outstanding source zero-reserve survivor full cash ceiling 1569d325.
-- source:
--   Pinned Mathlib lintegral_mono_set' and ae_iff; exact original paymentTimes definition and source initial atom vanish lemma 2a0a1444.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb32_original_truncated_paymentTimes_cash_le_full_positive_time_of_zero_initial_atom
    (σ : ℝ≥0∞) (μ : Measure ℝ)
    (hAtom : μ ({0} : Set ℝ) = 0)
    (b T : ℝ) (hbT : b ≤ T)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ ∩ Iio b, f t ∂μ) ≤
      (∫⁻ t in Ioc (0 : ℝ) T, f t ∂μ) := by sorry
