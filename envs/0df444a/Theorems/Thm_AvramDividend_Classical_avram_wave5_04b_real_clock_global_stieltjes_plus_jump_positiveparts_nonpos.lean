-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_global_stieltjes_plus_jump_positiveparts_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_real_clock_global_stieltjes_plus_jump_positiveparts_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:02:08.80832+00:00
-- url     : https://prove2.me/theorems/1aee230d-3909-4267-a4a4-c4e3f2e1220b
-- title:
--   No-summability actual global Stieltjes and real-clock right-jump positive-parts estimate
-- statement:
--   At every closed horizon before ruin or time zero, for every positive finite/infinite cap, the full actual dividendMeasure discounted Stieltjes mass plus the cap-linear terminal value reduction plus the ENNReal tsum of positive parts of all original chronological w right-payment residuals (converted back to real) is nonpositive. The real-clock set may contain arbitrarily countably many payments, including at zero and cap, and no summability or derivative at boundary or strict interior localisation is required. This is a sign estimate, not an identification of the full Ito-Meyer chain rule.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_countable_right_positive_part_zero
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal BigOperators
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- Summability-free real-clock joint nonpositive control of the complete actual closed-horizon Stieltjes mass and the absolutely summable countable explicit-w right-payment correction, with no reserve-interior localisation. -/
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
--       : ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
--         ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
--         (V (x + X.X T ω - rightLimit D T ω) -
--           V (x + X.X T ω))) +
--       (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
--         ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω -
--             (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
--           w (riskProcess X x D ((t : ℝ).toNNReal) ω)))).toReal ≤ 0 := by
--     have hContinuous := avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
--       X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       D hD ω T hPre
--     have hRightJumps := avram_wave5_04b_real_clock_countable_right_positive_part_zero
--       X x D w ω q hjump A hCount hNonneg hA
--     simpa [hRightJumps] using hContinuous

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_countable_right_positive_part_zero

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_real_clock_global_stieltjes_plus_jump_positiveparts_nonpos

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
    : ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω))) +
    (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))).toReal ≤ 0 := by sorry
