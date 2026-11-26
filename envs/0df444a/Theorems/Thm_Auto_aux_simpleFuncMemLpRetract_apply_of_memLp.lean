-- Prove2me | Theorems.Thm_Auto_aux_simpleFuncMemLpRetract_apply_of_memLp
-- name    : Auto.aux_simpleFuncMemLpRetract_apply_of_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:14.563869+00:00
-- url     : https://prove2.me/theorems/a725d4b7-fa8d-5040-a3b1-2c1d2e2e4c9a
-- title:
--   Auto: aux simple Func Mem Lp Retract apply of mem Lp
-- statement:
--   The chosen core retraction is the identity on an integrable simple function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8562-L8570
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8562-L8570

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

theorem Auto.aux_simpleFuncMemLpRetract_apply_of_memLp {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) (f : SimpleFunc X ℂ)
    (hf : MemLp (f : X → ℂ) p μ) :
    aux_simpleFuncMemLpRetract p μ f =
      ⟨f, hf⟩ := by sorry
