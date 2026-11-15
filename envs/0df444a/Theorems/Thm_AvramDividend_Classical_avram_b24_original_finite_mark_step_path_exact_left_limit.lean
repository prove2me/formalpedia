-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_mark_step_path_exact_left_limit
-- name    : AvramDividend.Classical.avram_b24_original_finite_mark_step_path_exact_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:05:28.76792+00:00
-- url     : https://prove2.me/theorems/33cd02fb-024a-419a-87e7-afc7a2f5c48b
-- title:
--   Actual finite original marked step source has the exact strict-left full sum as its left-time limit
-- statement:
--   For any finite original physically marked jump set S and real smallmark values z, at each strictly positive contact time t, the full right-inclusive chronological finite-step jump source sum over u≤v converges from the left at v↑t to the strict-left sum over u<t. This combines the Proved original causal single-mark step left limit across a finite genuine activity support. Together with the Proved B24 terminal marked atom difference, it identifies the exact original negative-mark jump at ruin from the physical source, rather than assuming it vanishes.
-- source:
--   Proved a30 original causal single marked step left limit and pinned finset Tendsto sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_left_limit_20261114
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finite_mark_step_path_exact_left_limit
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun v : ℝ≥0 =>
      ∑ u ∈ S, if u ≤ v then z u else 0)
      (𝓝[<] t) (𝓝 (∑ u ∈ S, if u < t then z u else 0)) := by sorry
