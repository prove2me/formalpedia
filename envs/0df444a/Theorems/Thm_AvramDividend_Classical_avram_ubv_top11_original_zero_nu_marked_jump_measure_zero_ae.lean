-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae
-- name    : AvramDividend.Classical.avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:42:33.46256+00:00
-- url     : https://prove2.me/theorems/aee42254-6467-48d3-af24-c2c7590b1e39
-- title:
--   Original zero-Lévy-measure source marked jump measure vanishes almost surely
-- statement:
--   Under vanishing original Lévy jump intensity, the actual intrinsic marked jump-counting measure of the unchanged original spectrally negative Lévy process is the zero measure on one probability-one event. It is constructed as count restricted to actual nonzero positive-time jump marks followed by the literal time-mark map.
-- source:
--   Proved e847d9a7 supplies all-positive-time original jump-mark zero on one full-measure event. Mathlib zero restriction and mapping give the exact original marked measure identity used by same-space Ito-Meyer compensated-jump source results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))) :
    ∀ᵐ ω ∂P, NX ω = 0 := by sorry
