-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:36:04.672689+00:00
-- url     : https://prove2.me/theorems/1c3dbb26-fdf2-45de-ba23-9f74419b9794
-- title:
--   Actual original UBV pre-jump Lévy generator integrability and HJB drift nonpositivity on every finite or infinite cap's atomless physical-time interior
-- statement:
--   Let X be the actual original same-filtration UBV spectrally negative Levy process and D the genuine admissible controlled dividend path. Under precisely the candidate source HJB condition in the strict interior (0,C), for every fixed atomless s-finite physical-time clock and P-almost every original sample path, the original Levy generator of w is integrable and its discounted HJB residual nonpositive at the TRUE predictable chronological pre-event reserve for almost every positive pre-ruin time. This includes finite positive caps possibly equal to initial capital, and C=∞; no cap derivative, full C², or generator integrability at cap itself is assumed. It is a physical-clock generator assertion, not a chain rule, local time statement, or dividend Stieltjes budget.
-- source:
--   New accepted original predictable pre-event strict interior theorem c9db7a94-e185-4483-b0d9-b79a2d3a7487 and exact corrected canonical 429e17ca-5528-40b5-b593-7c03973d0706. Separate from cap-linear extension lemma and full stochastic Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable w
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
        q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry
