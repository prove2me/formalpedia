-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b114_original_nonzero_source_jump_iff_some_negative_cutoff
-- name    : AvramDividend.Classical.avram_b114_original_nonzero_source_jump_iff_some_negative_cutoff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:17:08.548198+00:00
-- url     : https://prove2.me/theorems/3b3ab12d-f6ac-4b64-9427-e4c944cf9ab4
-- title:
--   A genuine nonzero original source jump occurs in a physical stopped cell exactly when some original negative cutoff detects a jump
-- statement:
--   For every sample path of the exact original spectrally negative Levy process and any physical half-open time interval, there exists a nonzero source left-limit jump in the interval if and only if there exist an original mark cutoff index n and source jump time in the interval with negative mark at most -1/(n+1). Forward direction uses the original all-time canonical left-limit theorem, the original noPosJumps field, and cofinal reciprocal thresholds; reverse direction uses strict negativity of the cutoff threshold. This equivalence identifies actual physical marked cells with the union of negative-mark Poisson cutoff occupancy events, with no independent process, no a.e. strengthening and no global negative-jump second moment.
-- source:
--   Original SpectrallyNegativeLevy.noPosJumps, Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times, reciprocal cutoff convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine nonzero original source jump in a half-open cell is exactly detected by some negative cutoff band. -/

theorem AvramDividend.Classical.avram_b114_original_nonzero_source_jump_iff_some_negative_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ↔
    (∃ n : ℕ, ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))) := by sorry
