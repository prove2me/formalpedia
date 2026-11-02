-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_ruin_clock_generator_residual_nonpos
-- name    : AvramDividend.Classical.avram_wave5_03_actual_discounted_ruin_clock_generator_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:34:10.523714+00:00
-- url     : https://prove2.me/theorems/a6c40351-b25e-4a98-bf9a-13fc031ec47e
-- title:
--   Actual controlled Lévy discounted finite-clock generator supersolution drift is nonpositive on a strict interior predictable region
-- statement:
--   On the original spectrally negative Lévy path and its actual adapted dividend control, the source generator residual Γw−qw is integrated against the genuine predictable observation measure after multiplication by exp(−qt) 1_{t≤T}1_{t≤ruinTime}. Under exactly the BV/UBV core's separate generator supersolution and explicit integrability plus strictly interior localisation on the active measurable set, this drift integral is nonpositive. The source pre-jump reserve is the strict left limit of x+X−rightLimit D; no independent process, HJB maximum equality, nonnegative w outside the active region, compensation, martingale or Ito chain rule is assumed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), deterministic sign of source generator drift within (5.11)–(5.13). Integrator bridge for canonical BV ef7e6c20-a118-46f0-ac94-5b02204bba49 and corrected UBV 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_discounted_ruin_clock_generator_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (A : Set (ℝ≥0 × Ω))
    (hA : MeasurableSet[𝓕.rightCont.predictable] A)
    (hregion : ∀ p ∈ A,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
              (1 : ℝ) else 0)
         else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      A μ) :
    (∫ p in A,
      (if p.1 ≤ T then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
            (1 : ℝ) else 0)
       else 0) *
      (X.generator w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) ≤ 0 := by sorry
