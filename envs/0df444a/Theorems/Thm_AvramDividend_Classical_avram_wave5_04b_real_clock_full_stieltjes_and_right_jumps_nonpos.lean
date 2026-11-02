-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_full_stieltjes_and_right_jumps_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_real_clock_full_stieltjes_and_right_jumps_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:49:19.085197+00:00
-- url     : https://prove2.me/theorems/948c90ac-65e9-4c9d-8d6e-06eabeac10df
-- title:
--   Original real-clock full Stieltjes and countable right-jump signed estimate without hloc
-- statement:
--   The genuine discounted closed-horizon dividend Stieltjes mass, cap-linear source-frozen terminal V reduction, and absolutely summable countable original w right-payment corrections indexed by the exact real clock together have nonpositive signed total. The countable real-time set is nonnegative and before ruin or time zero, including zero/cap payments and prepayment states above the cap. Actual D measure controls singular-continuous, diffuse and atomic variation; no strict-interior hloc.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal BigOperators
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- Real-clock joint signed control of the complete actual closed-horizon Stieltjes mass and the absolutely summable countable explicit-w right-payment correction, with no reserve-interior localisation. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
--       (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ)
--       (hD : IsAdmissibleLe X x C D)
--       (ω : Ω) (T : ℝ≥0)
--       (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
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
--       ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
--         ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
--         (V (x + X.X T ω - rightLimit D T ω) -
--           V (x + X.X T ω))) +
--       (∑' t : A, Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω))) ≤ 0 := by
--     have hContinuous := avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--       X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       D hD ω T hPre
--     have hRightJumps := avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos
--       X x D w ω q hjump A hCount hNonneg hA hSummable
--     linarith only [hContinuous, hRightJumps]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_real_clock_countable_right_signed_sum_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_real_clock_full_stieltjes_and_right_jumps_nonpos

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
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
    ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω))) +
    (∑' t : A, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω))) ≤ 0 := by sorry
