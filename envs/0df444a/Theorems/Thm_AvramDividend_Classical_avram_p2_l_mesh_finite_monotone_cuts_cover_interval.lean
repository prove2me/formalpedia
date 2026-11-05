-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_monotone_cuts_cover_interval
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_monotone_cuts_cover_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:45:14.92917+00:00
-- url     : https://prove2.me/theorems/3f30ed6d-bcfb-4b9f-b57c-9d2b747dd53f
-- title:
--   Finite successor half-open cells cover every value between the first and last cut
-- statement:
--   For any finite real sequence of endpoint cuts whose first value lies strictly below z and whose last value is at least z, some successor interval (p_i,p_(i+1)] contains z. This cover fact holds even without monotonicity; selecting the first index whose endpoint crosses z gives a constructive finite proof, and it closes the geometric cover obligation in the compact-test mesh approximation.

import Mathlib

open Set

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_monotone_cuts_cover_interval
    {n : ℕ} (p : Fin (n + 1) → ℝ) (z : ℝ)
    (hleft : p 0 < z) (hright : z ≤ p (Fin.last n)) :
    ∃ i : Fin n, z ∈ Ioc (p i.castSucc) (p i.succ) := by sorry
