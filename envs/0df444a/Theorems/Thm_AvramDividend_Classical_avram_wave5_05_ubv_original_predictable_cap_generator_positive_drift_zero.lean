-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:52:13.5101+00:00
-- url     : https://prove2.me/theorems/3a1a5bd7-61f2-4bea-8bc4-efdddcc1b071
-- title:
--   Actual predictable original UBV cap-linear generator has zero positive discounted drift integral
-- statement:
--   For the genuine original capped UBV dividend process, starting at cap and recurrent cap contact allowed, the positive part of the discounted compensated source-generator drift of the slope-one cap continuation, evaluated at the exact chronological predictable pre-event reserve leftLim(x+X−rightLimit D), has zero integral over strictly positive surviving times of any s-finite atomless physical-time clock. Only the strictly interior generator HJB is assumed for w; no cap derivative or C2 at c is assumed. The same-filtration strategy and admissibility are explicit. The claim does not eliminate local-time or dividend Stieltjes clocks.
-- source:
--   Proved book-reserve positive-generator drift zero 0df105e8-3ebf-4265-b9ad-4bea8c45af1d, Proved original chronological predictable/current identity 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d, slope-one generator equality de1c1aee-43d3-47a2-83ae-6115b56249e3, corrected core untouched 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hStrategy : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
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
