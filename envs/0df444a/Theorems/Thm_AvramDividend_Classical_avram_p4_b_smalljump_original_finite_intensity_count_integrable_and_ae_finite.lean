-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:20:11.292589+00:00
-- url     : https://prove2.me/theorems/eb8415ac-c2f7-4fa0-85c0-d83093b1830c
-- title:
--   Actual Lévy finite-intensity marked count has finite real first moment and is finite almost surely
-- statement:
--   The original intrinsic Lévy marked count on (s,t]×B is real integrable and finite P-almost surely when its measurable exact original count has the physical rate (t−s)X.ν(B) and the Lévy mass ν(B) is finite. These conclusions directly discharge the real-centred finite-band martingale input without introducing any Poisson surrogate.
-- source:
--   Mathlib ENNReal.mul_ne_top, integrable_toReal_of_lintegral_ne_top and ae_lt_top, applied to the actual source NX count and ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (hMeas : Measurable J)
    (hRate : (∫⁻ ω, J ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFinite : X.ν B ≠ ⊤) :
    Integrable (fun ω => (J ω).toReal) P ∧
      (∀ᵐ ω ∂P, J ω < ⊤) := by sorry
