-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_right_payment_finite_signed_sum_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_right_payment_finite_signed_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:28:22.079374+00:00
-- url     : https://prove2.me/theorems/3932cc62-e61e-450a-8926-545eabb694c7
-- title:
--   Original-source finite right-payment signed dividend correction without boundary localisation
-- statement:
--   For any finite set of actual chronological right dividend-payment times, including time zero and times with pre-payment reserve at or above the cap, the discounted signed sum of paid amounts plus w post-minus-pre drops is nonpositive. The sole mathematical assumption is the canonical explicit lump-sum drop inequality at zero or pre-ruin times; no hloc or derivative evaluation at either boundary is used.
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
--   /-- Arbitrary finite chronological right-payment corrections are nonpositive, including time zero and payments with pre-payment reserve above the cap. -/
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
--       (F : Finset ℝ≥0)
--       (hF : ∀ t ∈ F,
--         t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
--       (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D t ω - D t ω) +
--           w (riskProcess X x D t ω -
--             (rightLimit D t ω - D t ω)) -
--           w (riskProcess X x D t ω))) ≤ 0 := by
--     apply Finset.sum_nonpos
--     intro t ht
--     have hDrop := hjump t (hF t ht)
--     have hResidual :
--         (rightLimit D t ω - D t ω) +
--           w (riskProcess X x D t ω -
--             (rightLimit D t ω - D t ω)) -
--           w (riskProcess X x D t ω) ≤ 0 := by
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

theorem AvramDividend.Classical.avram_wave5_04b_original_right_payment_finite_signed_sum_nonpos
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
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ F,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by sorry
