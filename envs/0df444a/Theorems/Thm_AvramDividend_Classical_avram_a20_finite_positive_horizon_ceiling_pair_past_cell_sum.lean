-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum
-- name    : AvramDividend.Classical.avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:54:49.195901+00:00
-- url     : https://prove2.me/theorems/d18fc822-51c6-4277-8a2f-ebc2facdd47b
-- title:
--   Arbitrary finite positive-horizon event times have exact uniform ceiling-grid chronological pair-count decomposition
-- statement:
--   Any finite set F of strictly positive event times within a horizon T has its uniform-grid ceiling-index strictly ordered pair cardinal exactly equal to the sum over mesh cells of earlier-event-count times current-cell event-count. This is universal finite ordered-set combinatorics independent of the Lévy process. It uses the independently proved generic positive-horizon ceiling index bounds and the already Proved Mathlib finite-grid cross-pair cardinal identity, removing the earlier negative-cutoff sample-path restriction. It supports the actual original arbitrary-Borel marked jump factorial moment.

import Mathlib
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k)
    (hF : ∀ u ∈ F, 0 < u ∧ u ≤ T) :
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun u : ℝ≥0 =>
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
      (F.filter (fun v : ℝ≥0 =>
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card := by sorry
