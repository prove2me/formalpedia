-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_nat_count_stabilises_of_real_limit
-- name    : AvramDividend.Classical.avram_p2_l_mesh_nat_count_stabilises_of_real_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:56:11.204496+00:00
-- url     : https://prove2.me/theorems/4afd6166-ef37-4d22-b37b-16de2d1849bf
-- title:
--   Integer-valued finite-grid counts eventually equal their real limit
-- statement:
--   For natural-number counts along the uniform mesh, if their real casts converge to a finite natural-number limit, then the counts are exactly that limit for all sufficiently fine meshes. This upgrades finite-grid indicator count convergence to eventual equality after the true grid counts are identified as natural numbers, without any measure-theoretic assumption.

import Mathlib

open Filter Topology Set

theorem AvramDividend.Classical.avram_p2_l_mesh_nat_count_stabilises_of_real_limit (counts : ℕ → ℕ) (m : ℕ)
    (h : Tendsto (fun n : ℕ => (counts n : ℝ)) atTop (𝓝 (m : ℝ))) :
    ∀ᶠ n in atTop, counts n = m := by sorry
