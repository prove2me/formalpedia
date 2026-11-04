-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_ruin_truncation_allcap_predictable_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_ruin_truncation_allcap_predictable_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:44:59.706733+00:00
-- url     : https://prove2.me/theorems/f953c3e4-bc4c-4b35-bf08-64f0476f31be
-- title:
--   Actual original min(ruin,n).toNNReal clocks uniformly inherit predictable all-cap source generator HJB a.e.
-- statement:
--   For the exact canonical original clock τ_n=(min(ruinTime X x D,n)).toNNReal, a single probability-one event ensures for every n and μ-a.e. strictly positive preclock real time, the true original predictable pre-event left reserve lies in the generator domain and satisfies the original interior HJB sign, for any nonzero extended cap C, including infinity. No surrogate process, atom suppression or assumption of stochastic-integral L1. Uses source original truncation inequality and source original chronological predictable strict interior.
-- source:
--   c9db7a94-e185-4483-b0d9-b79a2d3a7487; 6b7a13a0-fa75-494d-8d56-b14562c66491; exact canonical original τ from 0dda1be7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At all exact finite original ruin clocks, original predictable HJB holds on a common P-conull set. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_ruin_truncation_allcap_predictable_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t →
      (t : ℝ≥0∞) <
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry
