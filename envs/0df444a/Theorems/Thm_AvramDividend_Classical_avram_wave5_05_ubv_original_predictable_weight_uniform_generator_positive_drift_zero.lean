-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_weight_uniform_generator_positive_drift_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_weight_uniform_generator_positive_drift_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:48:41.631678+00:00
-- url     : https://prove2.me/theorems/8b7bcf8d-6098-45bd-a7fd-6a3af281f3b0
-- title:
--   Every weighted positive predictable generator drift vanishes on one original UBV source conull event
-- statement:
--   For genuine capped unbounded-variation spectrally negative Levy source and admissible same-filtration dividend strategy, candidate w C2 only strictly below the cap, the positive part of discounted compensated generator drift of the slope-one cap continuation at the true predictable chronological pre-event reserve has zero weighted physical-clock lintegral for every nonnegative possibly infinite and path-dependent weight. One P-full event supports all weights simultaneously, including random discounting and stopped-window indicators, with any fixed s-finite atomless physical clock. Initial or repeated cap contact is allowed; no endpoint derivative, no dividend-payment strict-subcap assumption, and no claim that singular local time or dividend Stieltjes mass is zero.
-- source:
--   Proved canonical-admissibility-only predictable original cap-generator HJB target be7fa9d3-bc44-404a-8b5b-41a18ab5d562; source generator extension de1c1aee-43d3-47a2-83ae-6115b56249e3 and inclusive cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c. Supports corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_weight_uniform_generator_positive_drift_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (weight : ℝ≥0 → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, weight t ω * ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
              q * (if Function.leftLim
                    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
                w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
              else w c + (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c))
          else 0) ∂μ) = 0 := by sorry
