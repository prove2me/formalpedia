-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:42:32.180298+00:00
-- url     : https://prove2.me/theorems/44240348-bbdc-4c54-a971-8717ccbd2a60
-- title:
--   Canonical original real-clock countable signed right-payment correction without hloc
-- statement:
--   For a nonnegative countable set A of real time indices, all at time zero or before ruin, the actual absolutely summable signed real correction of chronological right-payment w drops has nonpositive total. Prepayment reserves may exceed the cap. Explicit summability ensures proper real series semantics. No hloc, reserve-interior, or differentiation hypothesis.
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
--   /-- The real-clock absolutely summable countable chronological right-payment signed correction is nonpositive at every boundary and at time zero. -/
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
--       (hSummable : Summable (fun t : A => Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) :
--       (∑' t : A, Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω))) ≤ 0 := by
--     apply tsum_nonpos
--     intro t
--     have hDrop := hjump ((t : ℝ).toNNReal) (hA t)
--     have hResidual :
--         (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω) ≤ 0 := by
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

theorem AvramDividend.Classical.avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos

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
    (hSummable : Summable (fun t : A => Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) :
    (∑' t : A, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω))) ≤ 0 := by sorry
