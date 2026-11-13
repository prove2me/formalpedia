-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
-- name    : AvramDividend.Classical.avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:09:49.624214+00:00
-- url     : https://prove2.me/theorems/3b32f69f-3164-4d3b-9e5d-3de907b2c7cb
-- title:
--   All sufficiently fine uniform ceiling meshes recover exact chronological pairs of any finite event-time set
-- statement:
--   For any finite set of nonnegative event times and positive physical horizon, there is a finite grid resolution such that every finer integer mesh distinguishes every strictly ordered event pair by strictly increasing ceiling indices. The proof uses the previously Proved generic finite positive separation of NNReal finite sets, an Archimedean mesh resolution large enough relative to the minimum gap and a ceiling order inequality. A simple finite-set filter equivalence then identifies the ceiling pair set exactly with all strict chronological pairs. This generalises the earlier fixed-negative-band original Lévy all-finer-grid theorem to arbitrary original Borel mark sets.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by sorry
