-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_eventually_at_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_eventually_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:01:58.550134+00:00
-- url     : https://prove2.me/theorems/a50ec6e7-521b-481b-85a7-622a9752e8e8
-- title:
--   Genuine original negative-jump band is pathwise empty at sufficiently small horizons
-- statement:
--   For each actual original spectrally negative Lévy sample path and each fixed negative mark band ending at -1/(n+1), all sufficiently early stopped marked-jump rectangles have zero source count. Uses only the original pathwise finite-separated-jump result and the accepted original marked-band void iff equivalence; no surrogate Poisson process. Establishes the pathwise continuity-at-zero fact for the genuine source-band void semigroup.
-- source:
--   W7-06 original-process compensation and small-time void law aa265c9f-4568-4639-9694-5ab319ddc374. Supports continuity of the actual marked void law and the L1/L2 martingale limit; on resubmission every imported source helper is authoritatively Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_band_no_early_source_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_eventually_at_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ T : ℝ≥0, T < ε →
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by sorry
