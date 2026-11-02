-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_positive_part_vanishes
-- name    : AvramDividend.Classical.avram_wave5_04b_original_countable_right_payment_positive_part_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:31:01.244776+00:00
-- url     : https://prove2.me/theorems/558326dc-0fef-4fb7-87b3-b8fc43693267
-- title:
--   Countably many original right-payment signed corrections have zero positive mass at all reserve contacts
-- statement:
--   For any countable set A of actual zero or pre-ruin right dividend times, the sum of ENNReal positive parts of discounted paid amounts plus w(post)-w(pre) is exactly zero, using the explicit original w-drop condition. No countable real summability, finite secant L, or strict reserve-interior localisation is assumed. The result includes the time-zero atom and pre-payment values above the cap.
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
--   /-- Every positive part of the entire countable chronological right-payment signed correction vanishes, without a summability or reserve-interior hypothesis. -/
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
--       (A : Set ℝ≥0) (hCount : A.Countable)
--       (hA : ∀ t : A,
--         (t : ℝ≥0) = 0 ∨
--           ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
--       (∑' t : A, ENNReal.ofReal (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω)))) = 0 := by
--     have hZero : ∀ t : A, ENNReal.ofReal (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω))) = 0 := by
--       intro t
--       have hDrop := hjump (t : ℝ≥0) (hA t)
--       have hResidual :
--           (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--             w (riskProcess X x D (t : ℝ≥0) ω -
--               (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--             w (riskProcess X x D (t : ℝ≥0) ω) ≤ 0 := by
--         linarith only [hDrop]
--       have hProduct : Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--           ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--             w (riskProcess X x D (t : ℝ≥0) ω -
--               (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--             w (riskProcess X x D (t : ℝ≥0) ω)) ≤ 0 :=
--         mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
--       exact ENNReal.ofReal_eq_zero.mpr hProduct
--     simp only [hZero, tsum_zero]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_original_countable_right_payment_positive_part_vanishes
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
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : A, ENNReal.ofReal (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) = 0 := by sorry
