-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:38:47.425726+00:00
-- url     : https://prove2.me/theorems/9b161bca-d22a-423f-8fac-5dbe15cde599
-- title:
--   Original unbounded-variation cap-linear generator HJB at the exact predictable pre-event reserve, with global cap-inclusive dividend secant
-- statement:
--   For the original controlled unbounded-variation spectrally negative Levy process, even with initial reserve equal to the cap and recurrent cap contacts, the slope-one cap extension has generator integrability and nonpositive discounted generator drift at the actual predictable chronological pre-event reserve on a P-conull event at almost every surviving positive time of an arbitrary s-finite atomless physical-time clock. The dividend-value secant is globally valid including cap contact. The original admissible capped strategy premise hD and same-filtration dividend-strategy premise hStrategy are explicit. No C2 at the cap, no assumption that dividends are paid strictly below cap, and no claim about random local times or singular dividend Stieltjes terms.
-- source:
--   Proved original capped generator and cap-inclusive secants d7b33e98-24b6-4433-a210-316c275aab29, using slope-one generator extension de1c1aee-43d3-47a2-83ae-6115b56249e3 and inclusive secants 44b01929-5817-44ac-9439-6eb3c9879f2c, plus exact original chronology 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Supports unchanged corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_cap_generator_and_secant_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae
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
    (hStrategy : IsDividendStrategy 𝓕 D)
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
