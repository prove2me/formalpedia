-- Prove2me | Theorems.Thm_Auto_aux_denseRange_integrableSimpleFuncToLp
-- name    : Auto.aux_denseRange_integrableSimpleFuncToLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:14.550353+00:00
-- url     : https://prove2.me/theorems/11ef4aea-a2be-5a5a-afb9-3f2fa6284e84
-- title:
--   Auto: aux dense Range integrable Simple Func To Lp
-- statement:
--   The common integrable simple-function core is dense in every finite ambient `Lp` space.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8775-L8789
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8775-L8789

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

theorem Auto.aux_denseRange_integrableSimpleFuncToLp {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    DenseRange (aux_integrableSimpleFuncToLp p μ hp_top) := by sorry
