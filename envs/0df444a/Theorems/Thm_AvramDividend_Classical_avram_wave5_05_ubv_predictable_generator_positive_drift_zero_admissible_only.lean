-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_predictable_generator_positive_drift_zero_admissible_only
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_predictable_generator_positive_drift_zero_admissible_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:43:21.167861+00:00
-- url     : https://prove2.me/theorems/98ddb79a-9f30-46be-a47c-83c7094b5ee8
-- title:
--   Actual predictable UBV cap-generator has zero positive drift mass under original capped admissibility alone
-- statement:
--   The original capped dividend admissibility hypothesis alone suffices to force the positive discounted compensated generator drift of the slope-one continuation to have zero integrated mass at the chronological predictable reserve on each s-finite atomless physical-time clock. The genuine admissibility hypothesis contains the required same-filtration strategy witness hD.1.1, so no separate strategy premise is added. Initial or later cap contact is admitted. w need only satisfy the strictly interior source-generator HJB, not C2 or a derivative at cap; singular local-time and Stieltjes controls remain outside scope.
-- source:
--   Accepted original predictable positive drift zero target 3a1a5bd7-61f2-4bea-8bc4-efdddcc1b071 and accepted strategy projection source b3117b07-8383-4143-a965-2d9876a04a99. The same original X,D and unchanged corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_predictable_generator_positive_drift_zero_admissible_only
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
