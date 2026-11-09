-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:07:39.716303+00:00
-- url     : https://prove2.me/theorems/54f74470-4b39-4385-ba7d-6adb83e58973
-- title:
--   Original zero-jump compensated marked stochastic source vanishes almost surely
-- statement:
--   Under vanishing Lévy jump intensity, the unchanged original-process marked counting measure and its negative-mark compensator both integrate every real-valued predictable or optional source to zero on a common probability-one event. The same-space compensated sum is therefore zero for any bounded clock, stochastic mask and source integrand.
-- source:
--   Proved aee42254 gives the zero intrinsic marked jump measure under ν=0; the compensating intensity is also zero, and both integral terms vanish without requiring integrability estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae
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
    ∀ᵐ ω ∂P,
      (∫ p, g ω p ∂(NX ω)) -
      (∫ t, ∫ z, g ω (t, z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂Λ) = 0 := by sorry
