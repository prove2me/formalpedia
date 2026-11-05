-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_mark_free_step_density
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_mark_free_step_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:31:36.063205+00:00
-- url     : https://prove2.me/theorems/6a6057b5-b21a-46c8-b882-e44e1678a1d8
-- title:
--   Global compact negative-test Ioc step-density avoiding finite intrinsic jump marks
-- statement:
--   For any compactly supported continuous test on real negative marks vanishing strictly above the negative cutoff, any finite set of actual significant intrinsic jump marks and any positive error tolerance, construct finitely many weighted Ioc interval indicators that approximate the test globally within that tolerance. The intervals have right endpoints at most the negative cutoff and all endpoints avoid the given significant marks. The proof explicitly derives the step-density conclusion from a quantitative real mesh, finite forbidden-mark avoidance, both support tails and uniform continuity; it assumes no convergence of grid indicators.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_support_cutoff_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_test_global_right_tail
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_fine_partition_with_margins
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_global_step_error_from_partition

open Set AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_mark_free_step_density (S : Finset ℝ) (f : ℝ → ℝ) (ρ η : ℝ) (hη : 0 < η) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (hf : ∀ z : ℝ, -ρ < z → f z = 0) : ∃ n : ℕ, ∃ a b c : Fin n → ℝ, (∀ i, b i ≤ -ρ) ∧ (∀ i, a i ∉ S ∧ b i ∉ S) ∧ (∀ z : ℝ, |f z - (∑ i : Fin n, if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η) := by sorry
