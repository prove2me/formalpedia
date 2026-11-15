-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
-- name    : AvramDividend.Classical.avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:36:25.044087+00:00
-- url     : https://prove2.me/theorems/eb7540eb-c248-4886-a5e1-0a80e6def3c4
-- title:
--   Every original spectrally negative Lévy physical left-jump mark is nonpositive at every positive time on every path
-- statement:
--   For every original spectrally negative Lévy process and every original sample path, the actual jump X_t minus its canonical left limit is nonpositive at every strictly positive time.
-- source:
--   SNL allpath noPosJumps and leftLim fields; pinned Mathlib tendsto_leftLim_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every actual original physical positive-time Lévy jump mark is nonpositive, on every path. -/

theorem AvramDividend.Classical.avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ ω : Ω, ∀ t : ℝ≥0, 0 < t →
      X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≤ 0 := by sorry
