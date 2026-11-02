-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_predictable_generator_hjb_countable_clocks_admissible_only
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_predictable_generator_hjb_countable_clocks_admissible_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:44:38.895206+00:00
-- url     : https://prove2.me/theorems/daab79d6-780a-4273-9658-481acce18683
-- title:
--   One P-full event supports original predictable cap HJB on countably many atomless clocks from capped admissibility alone
-- statement:
--   For the original capped unbounded-variation Levy dividend strategy, genuine capped IsAdmissibleLe and the usual strictly interior C2/HJB/gradient premises alone yield on a single P-conull event the cap-linear compensated generator integrability and nonpositive discounted generator drift at the true chronological predictable pre-event reserve, for almost every surviving positive time of each clock in any prescribed countable family of atomless s-finite physical-time clocks. Same-filtration strategy is extracted as hD.1.1, no separate hypothesis. Initial cap capital and repeated cap contacts are allowed. Singular local-time and dividend Stieltjes boundary measures remain separate.
-- source:
--   Accepted countable predictable cap generator target bce2dd31-a091-4806-b1fb-89db4f9fd857, admissibility projection hD.1.1 as verified in Proved b3117b07-8383-4143-a965-2d9876a04a99, unchanged corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_hjb_all_countable_atomless_clocks

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_predictable_generator_hjb_countable_clocks_admissible_only
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
