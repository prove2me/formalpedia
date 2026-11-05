-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_intrinsic_finite_test_difference_stability
-- name    : AvramDividend.Classical.avram_p2_l_mesh_intrinsic_finite_test_difference_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:53:14.495816+00:00
-- url     : https://prove2.me/theorems/a77d03ae-3b77-44d5-acee-812c00f6052a
-- title:
--   Finite intrinsic jump-test sum stability under uniform test approximation
-- statement:
--   For any finite collection of original càdlàg jump marks, uniformly approximating a real test by at most δ changes its intrinsic jump sum by at most the mark count times δ. This is a deterministic algebraic bridge to compact-test convergence.

import Mathlib

open Set Filter Topology
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_intrinsic_finite_test_difference_stability (Y : ℝ≥0 → ℝ) (S : Finset ℝ≥0)
    (f g : ℝ → ℝ) (δ : ℝ)
    (hδ : ∀ z : ℝ, |f z - g z| ≤ δ) :
    |(∑ u ∈ S, f (Y u - Function.leftLim Y u)) -
      (∑ u ∈ S, g (Y u - Function.leftLim Y u))| ≤
        (S.card : ℝ) * δ := by sorry
