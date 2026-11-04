-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_finite_nonlin_jump_variation_le_marks
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_localised_finite_nonlin_jump_variation_le_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:47:51.393059+00:00
-- url     : https://prove2.me/theorems/0e2c71a2-1f1b-465d-8380-0ac061ad3475
-- title:
--   Finite BV nonlinear original-source jumps dominated by negative mark variation
-- statement:
--   For any finite selection of BV source jump times, each with possibly different true controlled pre-source reserve u_i in [a+δ,b] and negative mark z_i in [-δ,0], the sum of the absolute nonlinear C1 increments is bounded by K times the sum of the absolute original jump marks, provided w is locally K-Lipschitz on [a,b]. This is a finite jump-sum estimate designed for the genuine finite-variation limit; it requires no global large-negative-jump moment and proves no independent stochastic compensator.
-- source:
--   Mathlib LipschitzOnWith.norm_sub_le and Finset.sum_le_sum

import Mathlib
open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_localised_finite_nonlin_jump_variation_le_marks {ι : Type*} (s : Finset ι) (w : ℝ → ℝ) (K : ℝ≥0) (a b δ : ℝ) (u z : ι → ℝ) (hδ : 0 ≤ δ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : ∀ i ∈ s, u i ∈ Icc (a + δ) b) (hz : ∀ i ∈ s, z i ∈ Icc (-δ) 0) : s.sum (fun i => |w (u i + z i) - w (u i)|) ≤ (K : ℝ) * s.sum (fun i => |z i|) := by sorry
