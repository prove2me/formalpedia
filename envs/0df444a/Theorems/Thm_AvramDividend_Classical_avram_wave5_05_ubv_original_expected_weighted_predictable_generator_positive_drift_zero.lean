-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_expected_weighted_predictable_generator_positive_drift_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_expected_weighted_predictable_generator_positive_drift_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:59:44.270431+00:00
-- url     : https://prove2.me/theorems/3befdbad-0396-46b9-b445-65e663560161
-- title:
--   Every nonnegative weighted expected predictable cap-generator positive-drift budget vanishes on original UBV source
-- statement:
--   For the genuine original capped UBV spectrally negative Levy reserve, only strictly interior C2/HJB and cap-inclusive gradient assumptions, the expectation over the original source law P of any arbitrary nonnegative possibly infinite path-dependent weighted physical-time positive discounted cap-linear generator drift at the actual predictable pre-event reserve is zero. This is uniform over all weights, including discount and restarted/stopped-window weights. Initial or recurrent cap contact is allowed and no endpoint C2 is used. It is the expected physical-clock generator budget, not the original controlled stochastic Itô–Meyer, martingale compensation or singular Stieltjes budget.
-- source:
--   Depends on accepted weight-uniform original predictable cap-generator drift-null theorem 8b7bcf8d-6098-45bd-a7fd-6a3af281f3b0; publish only after parent remotely Proved. Corrected core unchanged 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_weight_uniform_generator_positive_drift_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_expected_weighted_predictable_generator_positive_drift_zero
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
    ∀ (weight : ℝ≥0 → Ω → ℝ≥0∞),
      (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0,
        weight t ω * ENNReal.ofReal
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
          else 0) ∂μ ∂P) = 0 := by sorry
