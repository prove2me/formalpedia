-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_predictable_cap_generator_hjb_all_original_stopped_windows
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_predictable_cap_generator_hjb_all_original_stopped_windows
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:52:10.773557+00:00
-- url     : https://prove2.me/theorems/11477af8-3058-41d8-b399-34d66b16722c
-- title:
--   Original predictable cap-linear source generator HJB holds in every random stopped window on one conull event
-- statement:
--   For the actual original unbounded-variation capped spectrally negative Levy reserve and canonical admissible dividend control, the exact chronological predictable cap-linear compensated generator is integrable and has nonpositive discounted HJB drift at μ-almost every positive pre-ruin time belonging to ANY path-dependent stopping window, all such windows being quantified on one P-conull event. No adaptedness or measurability of the window is required since this is an a.e restriction theorem. It explicitly covers initial capital at cap, every recurrent cap hit and later restarted intervals without permanently stopping at first cap contact. w only needs C2 strictly interior, no cap derivative. Random local time and singular dividend Stieltjes terms remain outside the assertion.
-- source:
--   Accepted original predictable cap generator HJB under canonical admissibility be7fa9d3-bc44-404a-8b5b-41a18ab5d562, Proved recurrent cap-contact escape 7faa54d0-c54c-4c2d-b5b6-87bb8d2b0fbc, slope-one source generator de1c1aee-43d3-47a2-83ae-6115b56249e3 and inclusive secant 44b01929-5817-44ac-9439-6eb3c9879f2c. Core unchanged 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_predictable_cap_generator_hjb_all_original_stopped_windows
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
    ∀ᵐ ω ∂P, ∀ window : Ω → Set ℝ≥0,
      ∀ᵐ t : ℝ≥0 ∂μ,
        (t ∈ window ω ∧ 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
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
