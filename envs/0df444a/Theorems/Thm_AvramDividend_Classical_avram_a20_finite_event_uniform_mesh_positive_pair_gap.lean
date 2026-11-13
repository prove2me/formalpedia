-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_event_uniform_mesh_positive_pair_gap
-- name    : AvramDividend.Classical.avram_a20_finite_event_uniform_mesh_positive_pair_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:27:44.877846+00:00
-- url     : https://prove2.me/theorems/d9787044-72b5-4040-a08e-0c5893c84b85
-- title:
--   A single sufficiently fine uniform mesh separates every chronological pair of any finite nonnegative event-time set by a positive time gap
-- statement:
--   For any finite set F of nonnegative real event times and any nonnegative time horizon T, there exists a positive integer grid resolution k0 such that for every finer k and every u<v in F the physical time gap satisfies T<k(v−u). This is the generic source-independent finite pair gap selection lemma, using the Proved uniform positive separation of any finite NNReal set and Archimedean choice of k0. It is the exact interval-gap hypothesis needed to establish strict ceiling-grid chronological separation on arbitrary Borel original marked jump times.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_event_uniform_mesh_positive_pair_gap
    (F : Finset ℝ≥0) (T : ℝ≥0) :
    ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ u ∈ F, ∀ v ∈ F, u < v →
          (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by sorry
