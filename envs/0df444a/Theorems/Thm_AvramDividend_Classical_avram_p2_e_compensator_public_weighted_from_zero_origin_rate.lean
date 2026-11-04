-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_zero_origin_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-04T00:20:32.823767+00:00
-- url     : https://prove2.me/theorems/12ff9a1a-8374-40b1-8ada-93aaea66f712
-- title:
--   Original Lévy arbitrary past-weight predictable marked compensation from zero-origin separated ν rate
-- statement:
--   For the actual original spectrally negative Lévy process and any nonnegative weight W measurable at past time s, prove the exact ENNReal marked jump-count compensation on (s,t] for every Borel mark set from the sole independent source zero-origin separated-negative Lévy ν-rate. This connects public stochastic future-past factorisation and public negative-band monotone extension without assuming any compensator, replacing the process or imposing finite moments. Intended as a direct full weighted interface to P3/P4 after the separate rate is proved.
-- source:
--   Pinned Prove2Me public dependencies 8936f618, add050a6, 34dbea70 (Open), 42393902, a1baadce and original spectral-negative Lévy definition; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_reciprocal_borel_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_negative_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_zero_origin_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
