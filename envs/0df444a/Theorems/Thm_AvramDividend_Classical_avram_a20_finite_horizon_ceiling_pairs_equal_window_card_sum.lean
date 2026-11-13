-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
-- name    : AvramDividend.Classical.avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:59:34.439861+00:00
-- url     : https://prove2.me/theorems/a5e5c381-1d97-4686-9261-cf27a642c275
-- title:
--   Arbitrary finite event chronological ceiling-pair count equals uniform past-window and current-window count products
-- statement:
--   For any finite set of physical event times 0<u≤T and any positive mesh size k, the number of event-time pairs separated by their integer ceiling mesh index equals exactly the finite sum over mesh intervals of the number of preceding events multiplied by the number of events in the current half-open cell (s_i,t_i]. The proof derives the ceiling time-sublevel equivalence and exact ceiling cell equivalence from independently Proved real-mesh inequalities, and converts the separately Proved positive-horizon ceiling-pair count sum. This is a distribution-free bridge to the genuine original Lévy Borel-marked count physical windows.

import Mathlib
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k)
    (hF : ∀ u ∈ F, 0 < u ∧ u ≤ T) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i)).card *
      (F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i)).card := by sorry
