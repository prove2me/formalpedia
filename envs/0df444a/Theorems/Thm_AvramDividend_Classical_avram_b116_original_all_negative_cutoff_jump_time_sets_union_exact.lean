-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b116_original_all_negative_cutoff_jump_time_sets_union_exact
-- name    : AvramDividend.Classical.avram_b116_original_all_negative_cutoff_jump_time_sets_union_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:18:57.756551+00:00
-- url     : https://prove2.me/theorems/27bf23c9-6e63-42e3-8138-611f2edb9f16
-- title:
--   Union of every prescribed original negative-jump cutoff marked-time set equals exactly the physical original nonzero jump-time set
-- statement:
--   For every sample path of the exact original spectrally negative Levy source and any original half-open physical time interval (s,t], the union over all prescribed negative reciprocal mark cutoffs of actual source jump-time sets equals the exact set of all nonzero original source jumps on that interval. The pointwise proof first derives all-path nonpositivity from the original noPosJumps field and the Proved canonical all-time left limit, then detects every strictly negative nonzero jump at some cofinal cutoff. Conversely every negative cutoff mark is nonzero. This is a set equality rather than merely an existential interval statement, and is the physical count-exhaustion bridge for passing the negative-cutoff occupied-grid supremum to genuine original marked cells.
-- source:
--   Original SpectrallyNegativeLevy.noPosJumps, Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times, prescribed reciprocal cutoff limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original all-negative band cutoff sets exhaust exactly the physical nonzero jump times, for every original path and interval. -/

theorem AvramDividend.Classical.avram_b116_original_all_negative_cutoff_jump_time_sets_union_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (⋃ n : ℕ, {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}) =
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by sorry
