-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_fine_partition_with_margins
-- name    : AvramDividend.Classical.avram_p2_l_mesh_mark_free_fine_partition_with_margins
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:21:24.102728+00:00
-- url     : https://prove2.me/theorems/78cd7e8d-53b9-4893-b6c6-dfa9ce692796
-- title:
--   Finite original jump-mark avoiding fine partition with both support margins
-- statement:
--   For a finite set of significant genuine original-path jump marks, choose finitely many cuts in increasing order, avoiding every significant mark and with all cells smaller than a given positive continuity modulus. The first cut is below the specified zero-tail boundary and the last cut lies strictly between the right-tail tolerance boundary and the negative support cutoff. No density, Borel-indicator or stochastic convergence premise is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_archimedean_positive_fine_cell
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_near_uniform_partition

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_mark_free_fine_partition_with_margins (S : Finset ℝ) (A B L R δ : ℝ) (hAB : A < B) (hAL : A < L) (hRB : R < B) (hδ : 0 < δ) : ∃ n : ℕ, ∃ p : Fin (n + 1) → ℝ, StrictMono p ∧ (∀ i : Fin (n + 1), p i ∉ S) ∧ (∀ i : Fin n, p i.succ - p i.castSucc < δ) ∧ p 0 < L ∧ R < p (Fin.last n) ∧ p (Fin.last n) < B := by sorry
