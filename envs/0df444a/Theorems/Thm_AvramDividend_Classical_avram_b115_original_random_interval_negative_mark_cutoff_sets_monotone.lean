-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
-- name    : AvramDividend.Classical.avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:18:20.311263+00:00
-- url     : https://prove2.me/theorems/211d20b3-42f7-4047-ad07-bfe050d5ea90
-- title:
--   Original negative-jump cutoff time sets increase monotonically on each physical stopped interval
-- statement:
--   For arbitrary actual original source sample path and half-open physical interval (s,t], when mark cutoff n is no larger than m the set of actual original Lévy jump times whose jumps are at most -1/(n+1) is contained in the analogous set using threshold -1/(m+1). This follows directly from reciprocal monotonicity, preserving exact source and interval. This monotone inclusion is an input to finite stopped-grid occupied-cell count convergence and to the all-negative-band source exhaustion needed for the original Ito certificate.
-- source:
--   Original SpectrallyNegativeLevy physical jumps and prescribed negative reciprocal cutoffs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Prescribed negative-mark cutoff jump-time sets are monotone for the same original source physical interval. -/

theorem AvramDividend.Classical.avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ⊆
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((m : ℝ) + 1))} := by sorry
