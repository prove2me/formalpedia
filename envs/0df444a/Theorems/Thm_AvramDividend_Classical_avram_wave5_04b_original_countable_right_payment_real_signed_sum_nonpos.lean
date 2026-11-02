-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:32:26.121291+00:00
-- url     : https://prove2.me/theorems/dfb82109-3fc4-4efc-8c61-30724bbeac1c
-- title:
--   Original countable absolutely summable right-payment real correction without hloc
-- statement:
--   For a countable family of original dividend right-payment jump times at zero or before ruin, the absolutely summable real series of exponentially discounted paid amounts plus w(post)-w(pre) is nonpositive. It follows termwise from the canonical explicit w-drop hypothesis, including payments at zero/cap or with pre-payment reserve above cap, and does not assume strict interior occupation or a finite secant constant L. Summability is explicit to give the actual real series semantics.
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
--   /-- The complete absolutely summable countable chronological right-payment signed correction is nonpositive at every boundary and at time zero. -/
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
--           ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
--       (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω)))) :
--       (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
--     apply tsum_nonpos
--     intro t
--     have hDrop := hjump (t : ℝ≥0) (hA t)
--     have hResidual :
--         (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω) ≤ 0 := by
--       linarith only [hDrop]
--     exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
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
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
