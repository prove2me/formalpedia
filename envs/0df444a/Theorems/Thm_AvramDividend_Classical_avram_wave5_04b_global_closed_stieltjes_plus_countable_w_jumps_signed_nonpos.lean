-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_global_closed_stieltjes_plus_countable_w_jumps_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_global_closed_stieltjes_plus_countable_w_jumps_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:37:37.622746+00:00
-- url     : https://prove2.me/theorems/e196ee77-bd80-4be2-8820-4bce3c2e90ee
-- title:
--   Joint global Stieltjes and countable w-right-jump signed dividend correction without hloc
-- statement:
--   For admissible original dividends at arbitrary positive finite or infinite cap, the complete true discounted closed-horizon Stieltjes mass plus source-frozen cap-linear V reduction and the actual absolutely summable countable signed w right-payment corrections is nonpositive. The measure term includes diffuse and singular-continuous variation and the time-zero atom; the countable atom correction uses the explicit hjump bound even for pre-payment reserve above cap. No strict-interior hloc or derivative at zero/cap.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal BigOperators
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- Joint signed control of the complete actual closed-horizon Stieltjes mass and the absolutely summable countable explicit-w right-payment correction, with no reserve-interior localisation. -/
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
--       (A : Set ℝ≥0) (hCount : A.Countable)
--       (hA : ∀ t : A,
--         (t : ℝ≥0) = 0 ∨
--           ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
--       (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω)))) :
--       ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
--         ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
--         (V (x + X.X T ω - rightLimit D T ω) -
--           V (x + X.X T ω))) +
--       (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
--         ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
--           w (riskProcess X x D (t : ℝ≥0) ω -
--             (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
--           w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
--     have hContinuous := avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--       X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       D hD ω T hPre
--     have hRightJumps := avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
--       X x D w ω q hjump A hCount hA hSummable
--     linarith only [hContinuous, hRightJumps]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_global_closed_stieltjes_plus_countable_w_jumps_signed_nonpos
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
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) :
    ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω))) +
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
