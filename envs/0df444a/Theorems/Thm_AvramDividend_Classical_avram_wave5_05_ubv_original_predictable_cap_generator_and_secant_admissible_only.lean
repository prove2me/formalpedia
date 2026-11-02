-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:54:54.406286+00:00
-- url     : https://prove2.me/theorems/be7fa9d3-bc44-404a-8b5b-41a18ab5d562
-- title:
--   Original predictable UBV cap-generator HJB and cap-inclusive secant require only genuine capped admissibility
-- statement:
--   With no redundant separately assumed strategy witness, the original capped IsAdmissibleLe dividend strategy already yields the exact source generator-integrability and discounted HJB inequality at the chronological predictable pre-event reserve for each s-finite atomless physical clock, on a P-conull event at μ-a.e positive surviving time. Global all-time cap-inclusive dividend secants hold, including initial cap capital. The verification candidate is C2 only strictly inside (0,c). The strategy witness hD.1.1 is extracted from the already assumed genuine admissibility. No random local time or singular dividend Stieltjes conclusion.
-- source:
--   Parent Proved predictable original cap generator+secant theorem 9b161bca-d22a-423f-8fac-5dbe15cde599, Proved original admissibility projection usage b3117b07-8383-4143-a965-2d9876a04a99, source generator slope-one extension de1c1aee-43d3-47a2-83ae-6115b56249e3 and inclusive cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c. Corrected core untouched 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
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
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∀ a : ℝ, 0 ≤ a → a ≤ riskProcess X x D t ω →
        riskProcess X x D t ω - a ≤
          w (riskProcess X x D t ω) - w a) ∧
    (∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable
          (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator
          (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
        q * (if Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else w c + (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c)) ≤ 0) := by sorry
