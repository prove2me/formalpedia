-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:39:21.868521+00:00
-- url     : https://prove2.me/theorems/0ab6cc27-e0c3-4dcd-9d12-117219d20a88
-- title:
--   Actual original Lévy path jump-time support is null under every atomless time measure, including UBV
-- statement:
--   For every actual SpectrallyNegativeLevy P 𝓕 sample path and without any BV or finite-activity hypothesis, the set of genuine positive times with nonzero original jump ΔX_t(ω) has zero measure for every atomless time measure on nonnegative times, even path-dependent. This follows from the Proved original-path jump-time countability, and is the exact source atomless-time null-section interface for compensator Fubini and predictable time-integral comparisons. It is not the stronger assertion that the probability of a jump at each fixed time is zero, nor a Poisson time-mark law.
-- source:
--   Canonical original-path all-regime jump time countable theorem 741d3b5f-bfd0-434e-846c-b274123b5ebe, and Mathlib Set.Countable.measure_zero for Lebesgue measure on NNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (νt : Measure ℝ≥0) [NullSingletonClass νt] :
    νt {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0} = 0 := by sorry
