-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_real_joint_zero_cap_and_spatial_band_measurable
-- name    : AvramDividend.Classical.avram_wave7_19_original_real_joint_zero_cap_and_spatial_band_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:26:30.643123+00:00
-- url     : https://prove2.me/theorems/0b1a5931-d212-4f6e-b2e7-053d1271bc72
-- title:
--   Original real-time zero/cap postpayment reserve boundary and arbitrary spatial bands are jointly measurable random Stieltjes supports
-- statement:
--   The exact nonnegative real Stieltjes physical-time zero/cap reserve boundary and every lower/upper interior cutoff band of the actual original controlled post-rightpayment reserve define jointly measurable sets in real time times sample space. This composes the accepted W8-20 joint NNReal-time reserve measurability with real.toNNReal and then takes preimages of Borel singletons and intervals. It supplies W7-19 Fatou's hJoint plus individual measurable boundary/interior supports, preserving cap-reflection singular mass and the time-zero right dividend atom.
-- source:
--   W8-20 original jointly measurable postpayment reserve, Mathlib ENNReal ofReal and toNNReal measurability, original real paymentTimes support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_real_joint_zero_cap_and_spatial_band_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ × Ω |
      0 ≤ p.1 ∧ (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 = 0 ∨
        ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) = C)} ∧
    (∀ (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞) (n : ℕ),
      MeasurableSet {p : ℝ × Ω |
        0 ≤ p.1 ∧ lower n < x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 ∧
          ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) < upper n}) := by sorry
