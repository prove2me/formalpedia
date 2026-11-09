-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_compensated_marked_source_L1_center
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_L1_center
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:25:40.775866+00:00
-- url     : https://prove2.me/theorems/7896d927-7253-4e18-8c16-a3ffdf1dc2cd
-- title:
--   Original zero-jump compensated marked source is integrable and mean zero
-- statement:
--   For any path-dependent marked jump integrand and any physical clock intensity, the original-process compensated negative jump source is integrable and has expectation zero when the original Lévy jump intensity vanishes. The result uses the genuine intrinsic marked counting measure on the same probability space and needs no moment assumption on the integrand.
-- source:
--   Direct integrability and mean-zero corollary of Proved 54f74470, which identifies both original marked source terms as zero on one full-measure event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_L1_center
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
    (Λ : Measure ℝ≥0) (g : Ω → ℝ≥0 × ℝ → ℝ) :
    (let J : Ω → ℝ := fun ω =>
      (∫ p, g ω p ∂(NX ω)) -
      (∫ t, ∫ z, g ω (t, z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂Λ)
     Integrable J P ∧ (∫ ω, J ω ∂P) = 0) := by sorry
