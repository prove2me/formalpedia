-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_ruin_stopped_predictable_generator_gaussian_jump_integral_split
-- name    : AvramDividend.Classical.avram_wave5_03_original_ruin_stopped_predictable_generator_gaussian_jump_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:27:45.337977+00:00
-- url     : https://prove2.me/theorems/30a96e81-992f-4d6b-a08f-1d3ac062200c
-- title:
--   Original same-path ruin-stopped predictable integral of generator equals Gaussian plus compensated negative-jump generator drift
-- statement:
--   For the actual spectrally negative Lévy source X, its same capped admissible dividend D, same original ruinTime, real discount q and a finite NNReal clock T, integrate the source generator residual using exactly the right-continuous predictable stopped prepayment reserve and closed ruin/time indicators. Under explicit IntegrableOn of the Gaussian C2 drift and source jump/drift remainder over the actual predictable finite-clock region E, the full signed generator residual is the sum of these two true-source integrals. It imports the Proved original triplet algebra of Chat 03-A, preserves the original jump measure and filtration, and asserts no unproved stochastic martingale identity. Intended as the deterministic drift combining component of the full stopped controlled Itô–Meyer formula underlying both BV ef7e6c20 and corrected UBV 429e17ca.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped discounted generator identity. Direct companion to Proved original Gaussian generator split 668fd38f and Proved full-Stieltjes HJB drift bridge d73e3368, for BV ef7e6c20 and corrected UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_ruin_stopped_predictable_generator_gaussian_jump_integral_split
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
    (∫ p in E, (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
      (X.generator w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) - q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) =
    (∫ p in E, (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w
            (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) +
    (∫ p in E, (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
      (X.c * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
             (∫ z in Iio (0 : ℝ),
               SpectrallyNegativeLevy.generatorIntegrand w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) z ∂X.ν) -
             q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) := by sorry
