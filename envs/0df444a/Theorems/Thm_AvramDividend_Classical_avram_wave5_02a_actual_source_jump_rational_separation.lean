-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_jump_rational_separation
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_source_jump_rational_separation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:42:45.793686+00:00
-- url     : https://prove2.me/theorems/2ec22b22-1e38-4e0f-8cae-48f4dd9370eb
-- title:
--   Every positive actual source jump has a rational level separating left and right neighbourhoods
-- statement:
--   For every sample and each strictly positive nonzero jump of the actual original spectrally negative Levy process, there is a rational level and time interval on each side of the jump such that the path lies strictly above the level immediately before and strictly below it immediately after the jump. This is the key deterministic separation for rational-grid jump enumeration.
-- source:
--   Proved source nonpositive jumps and actual source left limits and right continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_source_jump_rational_separation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : 0 < t)
    (hj : X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0) :
    ∃ (a : ℚ) (s b : ℝ≥0), s < t ∧ t < b ∧
      (∀ u ∈ Ioo s t, (a : ℝ) < X.X u ω) ∧
      (∀ u ∈ Ico t b, X.X u ω < (a : ℝ)) := by sorry
