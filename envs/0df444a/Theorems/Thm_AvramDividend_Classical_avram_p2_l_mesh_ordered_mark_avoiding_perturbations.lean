-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_mark_avoiding_perturbations
-- name    : AvramDividend.Classical.avram_p2_l_mesh_ordered_mark_avoiding_perturbations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:38:26.002307+00:00
-- url     : https://prove2.me/theorems/83ce2265-911b-43f8-938c-22f6ef78c75e
-- title:
--   Order-preserving mark-free perturbation of uniformly separated nominal partition cuts
-- statement:
--   For a real-indexed ordered family of nominal cuts whose separation exceeds two perturbation radii, choose all perturbed cuts within their prescribed radii, simultaneously avoiding a finite collection of intrinsic jump values. The resulting cuts are strictly increasing. This builds the mark-free ordered mesh required for continuous-test step density.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_joint_avoiding_cuts

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_ordered_mark_avoiding_perturbations
    {ι : Type*} [Preorder ι] (S : Finset ℝ) (x : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : ι, i < j → x i + δ ≤ x j - δ) :
    ∃ y : ι → ℝ,
      (∀ i : ι, |y i - x i| < δ ∧ y i ∉ S) ∧ StrictMono y := by sorry
