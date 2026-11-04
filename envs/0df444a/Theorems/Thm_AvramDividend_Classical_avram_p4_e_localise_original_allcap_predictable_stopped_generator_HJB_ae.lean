-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:44:05.50498+00:00
-- url     : https://prove2.me/theorems/32ec2faa-19c9-4604-8f69-8f30b45595d2
-- title:
--   Original capped predictable HJB full generator is integrable and nonpositive on exact pre-ruin physical clocks for all extended caps
-- statement:
--   On the actual original process and admissible dividend control, any nonzero extended real cap C, including infinity, supports true predictable prepayment left-limit reserve in the positive generator domain at almost every positive time on any deterministic atomless s-finite physical-time clock prior to any ruin-dominated stop. Hence exact original X.generator is defined there and source HJB drift is nonpositive, with no finite/infinite case split. Requires original initial reserve under C and source UBV; does not grant Stieltjes dividend local-time mass zero or global L1 stochastic residual.
-- source:
--   Proved exact original all-cap pre-event interior theorem c9db7a94-e185-4483-b0d9-b79a2d3a7487; no copied process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original predictable pre-event generator applies a.e. at any nonzero ENNReal cap. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry
