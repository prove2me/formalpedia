-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_actual_stieltjes_integrable_forward_secant_real_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_actual_stieltjes_integrable_forward_secant_real_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:55:44.876447+00:00
-- url     : https://prove2.me/theorems/f3524bbb-9392-4b47-b613-29eeaebb77a0
-- title:
--   Actual integral signed derivative-free cap-contact Stieltjes forward-secant control
-- statement:
--   For any positive finite/infinite cap and arbitrary real discount, the signed real Bochner integral over the true closed-horizon dividendMeasure of the exponentially weighted forward secant residual δ + V(y)-V(y+δ), y being the original source-X postpayment reserve clipped at zero, is nonpositive whenever integrable. This includes the genuine singular-continuous and diffuse components, countable right-payment atoms, and time-zero atom, and evaluates no derivative at zero/cap. The integrand is a secant approximant and its identification with the stochastic chain-rule control term is delegated to Chat03.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The true dividend Stieltjes measure has a nonpositive integrable real signed
--   forward-secant correction, including diffuse, singular-continuous and time-zero
--   variation, without differentiating the candidate at either cap endpoint. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
--       (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
--       (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
--           (δ +
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
--         (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
--       (∫ s in Icc (0 : ℝ) (T : ℝ),
--         Real.exp (-(q * s)) *
--           (δ +
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by
--     have hPoint : ∀ s : ℝ, Real.exp (-(q * s)) *
--           (δ +
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
--             V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ≤ 0 := by
--       intro s
--       let y : ℝ := max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)
--       have hy : 0 ≤ y := le_max_left _ _
--       have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ.le
--       have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--         C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--         y (y + δ) hy hOrder
--       have hResidual : δ + V y - V (y + δ) ≤ 0 := by
--         linarith only [hSec]
--       exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
--     exact MeasureTheory.integral_nonpos_of_ae (Filter.Eventually.of_forall hPoint)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_actual_stieltjes_integrable_forward_secant_real_signed_nonpos

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Icc (0 : ℝ) (T : ℝ),
      Real.exp (-(q * s)) *
        (δ +
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)) -
          V (max 0 (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by sorry
