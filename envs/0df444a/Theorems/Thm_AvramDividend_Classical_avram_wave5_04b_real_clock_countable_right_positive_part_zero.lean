-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_countable_right_positive_part_zero
-- name    : AvramDividend.Classical.avram_wave5_04b_real_clock_countable_right_positive_part_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:49:36.971083+00:00
-- url     : https://prove2.me/theorems/a18b67aa-7809-4804-9270-072e49b9036a
-- title:
--   Every countable real-clock original right-payment positive correction vanishes without summability
-- statement:
--   For any countable set of nonnegative real payment times at zero or before ruin, the ENNReal sum of positive parts of the actual discounted original w right-payment signed residuals is exactly zero without a real-series summability hypothesis. The explicit chronological right-jump drop condition handles payments at reserve zero and cap and pre-payment reserves above the cap. This provides a summability-free bridge to genuine BV verification.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal BigOperators
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The countable real-clock positive part of all chronological right-payment signed corrections vanishes, with no summability condition. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
--       (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (ω : Ω) (q : ℝ)
--       (hjump : ∀ t : ℝ≥0,
--         (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
--         rightLimit D t ω - D t ω ≤
--           w (riskProcess X x D t ω) -
--             w (riskProcess X x D t ω -
--               (rightLimit D t ω - D t ω)))
--       (A : Set ℝ) (hCount : A.Countable)
--       (hNonneg : ∀ t : A, 0 ≤ (t : ℝ))
--       (hA : ∀ t : A,
--         ((t : ℝ).toNNReal) = 0 ∨
--           (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω)
--       : (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) = 0 := by
--     have hTerm : ∀ t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω))) = 0 := by
--       intro t
--       have hDrop := hjump ((t : ℝ).toNNReal) (hA t)
--       have hResidual :
--           (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--             w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--               (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--             w (riskProcess X x D ((t : ℝ).toNNReal) ω) ≤ 0 := by
--         linarith only [hDrop]
--       apply ENNReal.ofReal_eq_zero.mpr
--       exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
--     simp [hTerm]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_real_clock_countable_right_positive_part_zero

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (ω : Ω) (q : ℝ)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (A : Set ℝ) (hCount : A.Countable)
    (hNonneg : ∀ t : A, 0 ≤ (t : ℝ))
    (hA : ∀ t : A,
      ((t : ℝ).toNNReal) = 0 ∨
        (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω)
    : (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) = 0 := by sorry
