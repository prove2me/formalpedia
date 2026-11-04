-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:01:57.228663+00:00
-- url     : https://prove2.me/theorems/bcaba602-2503-4481-91e1-3b66b2c46f19
-- title:
--   Full negative pathwise jump count in ENNReal bounded by original uniform-grid indicators
-- statement:
--   For any real path on NNReal time and its actual negative jump set satisfying explicit time, strict-left-limit, right-continuity and jump-size assumptions, the full ENNReal conversion of the extended-natural jump count is bounded by the liminf of ENNReal original adjacent-grid negative increment indicator sums. The proof uses the accepted ENat all-jump bound and genuine pinned ENat-to-ENNReal preservation of liminf and finite indicator sums, without finite-activity, compensator, or rate assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_indicator_sum

open Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
    (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    ENat.toENNReal S.encard ≤ Filter.liminf (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℝ≥0∞) else 0)) atTop := by sorry
