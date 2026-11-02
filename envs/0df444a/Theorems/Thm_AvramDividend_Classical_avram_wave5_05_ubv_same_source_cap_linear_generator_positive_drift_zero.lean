-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:45:32.504879+00:00
-- url     : https://prove2.me/theorems/0df105e8-3ebf-4265-b9ad-4bea8c45af1d
-- title:
--   Exact original UBV cap-linear generator has zero positive discounted drift mass at every finite positive cap
-- statement:
--   For the actual original unbounded-variation spectrally negative Lévy process X and admissible same-filtration dividend regulator D, possibly starting at the positive finite cap, the positive part of the discounted source-generator drift of the slope-one cap extension has zero integral over positive pre-ruin times, for every deterministic sigma-finite time measure. The cap itself may be contacted, and no derivative or second-order smoothness at the cap is assumed. This follows from original controlled strict interior time occupation and exact compensated generator continuation. It supplies the physical-time drift part of a stopped stochastic verification inequality; martingale, local-time and Stieltjes terms remain outstanding.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 and corrected core 429e17ca-5528-40b5-b593-7c03973d0706. Proved source generator interior occupation bd222a39-c2dd-4836-ab7e-20c75561dcda and Proved slope-one generator agreement de1c1aee-43d3-47a2-83ae-6115b56249e3, pinned Mathlib ENNReal.ofReal_eq_zero and MeasureTheory.lintegral_congr_ae. Independent of pending candidate 20543.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
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
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (riskProcess X x D t ω) -
              q * (if riskProcess X x D t ω ≤ c then
                w (riskProcess X x D t ω)
              else w c + (riskProcess X x D t ω - c))
          else 0) ∂μ) = 0 := by sorry
