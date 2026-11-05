-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_perturbed_successor_gap_bound
-- name    : AvramDividend.Classical.avram_p2_l_mesh_perturbed_successor_gap_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:40:37.505574+00:00
-- url     : https://prove2.me/theorems/e3def667-17f2-40b6-b63d-4ac44bd83802
-- title:
--   Uniform mesh bound persists after small simultaneous mark-avoiding perturbations
-- statement:
--   For successive cuts of a finite real mesh, if every perturbed cut lies within radius r of its nominal location and every original adjacent cell has width at most h, then all perturbed adjacent cell widths are strictly less than h plus twice r. This quantitative bound ensures that finite marked-jump avoidance preserves the continuity modulus required by compact-test approximations.

import Mathlib

theorem AvramDividend.Classical.avram_p2_l_mesh_perturbed_successor_gap_bound
    {n : ℕ} (x y : Fin (n + 1) → ℝ) (r h : ℝ)
    (hwindow : ∀ i : Fin (n + 1), |y i - x i| < r)
    (hnom : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) :
    ∀ i : Fin n, y i.succ - y i.castSucc < h + 2 * r := by sorry
