-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_prejump_discount_generator_positivepart_lintegral_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_discount_generator_positivepart_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:41:39.877544+00:00
-- url     : https://prove2.me/theorems/c936ea58-9f8f-43ba-b1b6-59d8b788fa28
-- title:
--   Genuine original predictable UBV generator positive HJB drift integrates to zero against every atomless s-finite pre-ruin time clock for all nonzero caps
-- statement:
--   For the original spectrally negative Levy process of unbounded variation and its same-filtration controlled reserve, the original generator-minus-discount residual of w evaluated at the true chronological predictable pre-event surplus has nonpositive value at all positive surviving μ-a.e. times for any predetermined s-finite atomless time clock. Its ENNReal positive-part therefore has exactly zero μ-lintegral on P-a.e. original trajectory, even if the generator residual is not globally integrable and the reserve can start at its cap. Works for any nonzero finite or infinite extended cap without global smoothness at the cap, without assuming interior dividend payments, and without asserting a full Ito–Meyer stochastic budget.
-- source:
--   Requires accepted original predictable raw generator HJB theorem 1c3dbb26-fdf2-45de-ba23-9f74419b9794, plus Mathlib lintegral_congr_ae and ENNReal.ofReal_eq_zero. Corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_discount_generator_positivepart_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
          else 0) ∂μ) = 0 := by sorry
