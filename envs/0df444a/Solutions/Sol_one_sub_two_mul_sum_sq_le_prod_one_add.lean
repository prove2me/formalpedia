-- Prove2me | solution 1 for one_sub_two_mul_sum_sq_le_prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:00.574027+00:00
-- url     : https://prove2.me/submissions/0cf9821a-d0be-4b73-805b-08a4cc75cdc7

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients
public import Theorems.Thm_Real_exp_sub_two_mul_sq_le

set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1 / 2) (hsum : ∑ i ∈ s, a i = 0) :
    1 - 2 * ∑ i ∈ s, a i ^ 2 ≤ ∏ i ∈ s, (1 + a i) := by
  have key : Real.exp (∑ i ∈ s, (a i - 2 * a i ^ 2)) ≤ ∏ i ∈ s, (1 + a i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      fun i hi => Real.exp_sub_two_mul_sq_le (abs_le.mp (ha i hi)).1
  have hs : ∑ i ∈ s, (a i - 2 * a i ^ 2) = -(2 * ∑ i ∈ s, a i ^ 2) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.mul_sum]
    simp
  calc 1 - 2 * ∑ i ∈ s, a i ^ 2 = -(2 * ∑ i ∈ s, a i ^ 2) + 1 := by ring
    _ ≤ Real.exp (-(2 * ∑ i ∈ s, a i ^ 2)) := Real.add_one_le_exp _
    _ = Real.exp (∑ i ∈ s, (a i - 2 * a i ^ 2)) := by rw [hs]
    _ ≤ ∏ i ∈ s, (1 + a i) := key
