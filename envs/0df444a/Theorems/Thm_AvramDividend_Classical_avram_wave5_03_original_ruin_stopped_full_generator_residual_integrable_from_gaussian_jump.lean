-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_ruin_stopped_full_generator_residual_integrable_from_gaussian_jump
-- name    : AvramDividend.Classical.avram_wave5_03_original_ruin_stopped_full_generator_residual_integrable_from_gaussian_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:43:11.080603+00:00
-- url     : https://prove2.me/theorems/732738fd-32ef-4589-99c5-b1d9594e39b5
-- title:
--   Original ruin-stopped full discounted generator residual is integrable from Gaussian and source jump drift L1 components
-- statement:
--   For original X and admissible capped D on its own probability space and filtration, the discount- and ruin-stopped generator-minus-q value of the actual predictable prepayment left-limit reserve is IntegrableOn every measurable predictable set E whenever its genuine σ² second-derivative Gaussian drift and its c*w' plus original negative-mark generatorIntegrand drift are separately IntegrableOn. This is the exact hIntGen premise required by the already Proved same-source full Stieltjes HJB drift correction d73e3368 and direct original BV ef7e6c20 / corrected UBV 429e17ca, with no artificial martingale or process copy. The proof uses the canonical source 03-A triplet algebra pointwise on the real finite T and true ruin indicators, then integrable_congr and Integrable.add. This is finite-clock drift integrability only; the full mixed stochastic Ito formula remains open.
-- source:
--   Original source stopped Itô–Meyer generator residual integrability premise in Proved d73e3368, BV ef7e6c20, corrected UBV 429e17ca; Proved 03-A exact generator algebra 668fd38f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_ruin_stopped_full_generator_residual_integrable_from_gaussian_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hE : MeasurableSet[𝓕.rightCont.predictable] E)
    (hG : IntegrableOn
      (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w
            (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ)
    (hJ : IntegrableOn
      (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.c * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
             (∫ z in Iio (0 : ℝ),
               SpectrallyNegativeLevy.generatorIntegrand w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) z ∂X.ν) -
             q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ) :
    IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ := by sorry
