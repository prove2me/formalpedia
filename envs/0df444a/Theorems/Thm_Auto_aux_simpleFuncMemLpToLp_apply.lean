-- Prove2me | Theorems.Thm_Auto_aux_simpleFuncMemLpToLp_apply
-- name    : Auto.aux_simpleFuncMemLpToLp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:50.571606+00:00
-- url     : https://prove2.me/theorems/3f8602f3-cd7e-5c12-979a-dab7a0e7d71e
-- title:
--   Auto: aux simple Func Mem Lp To Lp apply
-- statement:
--   The core-to-`Lp` map sends an integrable simple function to its usual equivalence class.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8589-L8593
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8589-L8593

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

theorem Auto.aux_simpleFuncMemLpToLp_apply {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) (f : SimpleFunc X ℂ)
    (hf : MemLp (f : X → ℂ) p μ) :
    aux_simpleFuncMemLpToLp p μ ⟨f, hf⟩ = hf.toLp f := by sorry
