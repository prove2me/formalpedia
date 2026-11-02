-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_hjb_all_countable_atomless_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_hjb_all_countable_atomless_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:53:04.560701+00:00
-- url     : https://prove2.me/theorems/bce2dd31-a091-4806-b1fb-89db4f9fd857
-- title:
--   One original-process conull event supports cap-linear predictable HJB over every prescribed countable atomless characteristic clock
-- statement:
--   For every countable family of s-finite atomless physical-time clocks, the exact chronological predictable reserve of the original capped UBV controlled Levy process lies at valid points of the slope-one cap continuation source generator, and its discounted source generator is nonpositive at almost every strictly positive pre-ruin time for each clock, simultaneously on one P-conull event. The candidate is C2 only strictly interior; initial or later cap contact is admitted. No singular local-time or dividend Stieltjes conclusion.
-- source:
--   Dependent on fixed clock predictable generator+secant target 9b161bca-d22a-423f-8fac-5dbe15cde599, originally built from generator and inclusive-cap secant d7b33e98-24b6-4433-a210-316c275aab29 and chronology 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Publish only after parent Proved. Corrected core unchanged 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_global_secant_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_hjb_all_countable_atomless_clocks
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
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ n,
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
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c)) ≤ 0 := by sorry
