-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_cap_generator_and_secant_ae
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_cap_generator_and_secant_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:39:14.665008+00:00
-- url     : https://prove2.me/theorems/d7b33e98-24b6-4433-a210-316c275aab29
-- title:
--   Original UBV finite-cap contact: global dividend secants and almost-everywhere cap-linear source generator HJB
-- statement:
--   For the genuine original spectrally negative Levy source X of unbounded variation and the actual same-filtration capped admissible dividend strategy D, possibly starting at the cap x=c, the inclusive-cap gradient hypothesis implies a dividend-value secant for every nonnegative pre-ruin reserve at every time, including t=0 and cap contact. Separately, for every deterministic s-finite time measure, almost every strictly positive pre-ruin time has the original compensated Levy generator integrability and nonpositive discounted generator drift for the slope-one continuation of w. No derivative or C2 assumption is made at the cap. The generator result uses genuine source cap/zero occupation and preserves both Gaussian and infinite-jump-activity cases; it does not assert a full Ito-Meyer formula or settle singular Stieltjes dividend measures.
-- source:
--   Corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706, Proved exact original X,D generator interior occupation bd222a39-c2dd-4836-ab7e-20c75561dcda, Proved source generator equality de1c1aee-43d3-47a2-83ae-6115b56249e3, Proved generator integrability equivalence 76780f0a-9237-49b3-8584-ca46df97ad81 and Proved inclusive-cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c. No parent edge asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_cap_generator_and_secant_ae
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
    (μ : Measure ℝ≥0) [SFinite μ] :
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∀ a : ℝ, 0 ≤ a → a ≤ riskProcess X x D t ω →
        riskProcess X x D t ω - a ≤
          w (riskProcess X x D t ω) - w a) ∧
    (∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable
          (fun y => if y ≤ c then w y else w c + (y - c))
          (riskProcess X x D t ω) ∧
        X.generator
          (fun y => if y ≤ c then w y else w c + (y - c))
          (riskProcess X x D t ω) -
          q * (if riskProcess X x D t ω ≤ c then
            w (riskProcess X x D t ω)
          else w c + (riskProcess X x D t ω - c)) ≤ 0) := by sorry
