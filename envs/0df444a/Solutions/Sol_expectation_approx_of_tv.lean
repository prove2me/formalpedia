-- Prove2me | solution 1 for expectation_approx_of_tv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:55.776786+00:00
-- url     : https://prove2.me/submissions/5179178c-c74d-4749-8bcd-09174b981bda

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (f : H → Bool) (δ : ℝ)
    (hδ : tvDistance μ ν ≤ δ) :
    |boolTestExpectation μ f - boolTestExpectation ν f| ≤ δ := by
  simp only [boolTestExpectation, trueExpectation]
  calc |∑ h : H, μ.prob h * (if f h then (1 : ℝ) else 0) -
        ∑ h : H, ν.prob h * (if f h then (1 : ℝ) else 0)|
      = |∑ h : H, (μ.prob h - ν.prob h) *
          (if f h then (1 : ℝ) else 0)| := by
        congr 1; rw [← Finset.sum_sub_distrib]; congr 1; ext h; ring
    _ ≤ ∑ h : H, |(μ.prob h - ν.prob h) *
          (if f h then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h : H, |μ.prob h - ν.prob h| := by
        apply Finset.sum_le_sum; intro h _
        rw [abs_mul]
        apply mul_le_of_le_one_right (abs_nonneg _)
        split_ifs <;> simp
    _ = tvDistance μ ν := rfl
    _ ≤ δ := hδ
