-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_strict_partition_cell_sum_eq_sample
-- name    : AvramDividend.Classical.avram_p2_l_mesh_strict_partition_cell_sum_eq_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:35:33.739688+00:00
-- url     : https://prove2.me/theorems/74ad0e45-909f-48de-813e-030fe1134b81
-- title:
--   Unique active cell in a finite ordered intrinsic-mark step partition
-- statement:
--   For a finite family of real half-open intervals whose successive cells are ordered without overlap, a point lying inside one cell contributes exactly that cell's sampled coefficient to the finite interval-step sum. This is the algebraic identity required to turn a marked-test modulus into the uniform finite-step density estimate on the original jump marks.

import Mathlib

open Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_strict_partition_cell_sum_eq_sample
    {n : ℕ} (a b c : Fin n → ℝ)
    (hordered : ∀ i j : Fin n, i < j → b i ≤ a j)
    (z : ℝ) (i : Fin n) (hi : z ∈ Ioc (a i) (b i)) :
    (∑ j : Fin n, if z ∈ Ioc (a j) (b j) then c j else 0) = c i := by sorry
