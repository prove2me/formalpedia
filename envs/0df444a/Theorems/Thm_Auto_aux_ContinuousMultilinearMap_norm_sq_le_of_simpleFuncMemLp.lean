-- Prove2me | Theorems.Thm_Auto_aux_ContinuousMultilinearMap_norm_sq_le_of_simpleFuncMemLp
-- name    : Auto.aux_ContinuousMultilinearMap_norm_sq_le_of_simpleFuncMemLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:41.711027+00:00
-- url     : https://prove2.me/theorems/1bcdc0b8-a78e-5e0d-89d4-4ac1c47d0d2f
-- title:
--   Auto: aux Continuous Multilinear Map norm sq le of simple Func Mem Lp
-- statement:
--   A sharp squared estimate verified on the `MemLp` simple-function core extends to all
--   ambient `Lp` inputs.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8902-L8919
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8902-L8919

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto

theorem Auto.aux_ContinuousMultilinearMap_norm_sq_le_of_simpleFuncMemLp
    {ι X F : Type*} [Fintype ι] [MeasurableSpace X]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (C : ℝ)
    (hcore : ∀ x : ∀ i, aux_simpleFuncMemLpSubmodule (p i) μ,
      ‖B (fun i ↦ aux_simpleFuncMemLpToLp (p i) μ (x i))‖ ^ 2 ≤
        C * ∏ i, ‖aux_simpleFuncMemLpToLp (p i) μ (x i)‖ ^ 2) :
    ∀ g : ∀ i, Lp ℂ (p i) μ,
      ‖B g‖ ^ 2 ≤ C * ∏ i, ‖g i‖ ^ 2 := by sorry
