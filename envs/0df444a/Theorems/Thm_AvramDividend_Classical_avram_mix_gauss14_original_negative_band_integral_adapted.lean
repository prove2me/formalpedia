-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_negative_band_integral_adapted
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_negative_band_integral_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:33:36.546205+00:00
-- url     : https://prove2.me/theorems/680ad48c-87a4-4250-afc4-6c6cb48e8f53
-- title:
--   All negative Borel spatial-band real jump integrals are adapted in the original filtration
-- statement:
--   At each deterministic horizon, the original X signed jump integral over the genuine closed-right time window and an arbitrary Borel nonpositive spatial band is measurable in the original filtration. Apply the proved signed integral to negative lintegral conversion and the proved original arbitrary-weight positive marked-jump measurability. This directly feeds both physical small-jump bands (-1,-1/(n+1)] and large jumps (-infinity,-1], keeping the -1 boundary single-counted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_negative_band_integral_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∫ p in (Ioc (0 : ℝ≥0) T ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
