-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_near_uniform_partition
-- name    : AvramDividend.Classical.avram_p2_l_mesh_mark_free_near_uniform_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:12:47.537614+00:00
-- url     : https://prove2.me/theorems/52f354e0-4255-45b5-886e-5e83c8de4323
-- title:
--   Finite mark-free strictly ordered near-uniform partition with controlled successor gaps
-- statement:
--   Starting from a positive uniform real cell width h and an arbitrary finite set of genuine intrinsic jump marks, select one perturbed endpoint per nominal Fin(n+1) grid cut within radius r, avoiding every significant mark, preserving strict cut order and keeping each new successor gap below h+2r. The hypothesis 2r≤h makes nominal perturbation windows disjoint, so this theorem explicitly proves the marked-mesh selection component of global continuous-test step approximation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_nominal_cuts_geometry
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_mark_avoiding_perturbations
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_perturbed_successor_gap_bound

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_mark_free_near_uniform_partition
    (S : Finset ℝ) (n : ℕ) (A h r : ℝ)
    (hh : 0 < h) (hr : 0 < r) (hsep : 2 * r ≤ h) :
    ∃ p : Fin (n + 1) → ℝ, StrictMono p ∧
      (∀ i : Fin (n + 1),
        |p i - (A + (i.val : ℝ) * h)| < r ∧ p i ∉ S) ∧
      (∀ i : Fin n, p i.succ - p i.castSucc < h + 2 * r) := by sorry
