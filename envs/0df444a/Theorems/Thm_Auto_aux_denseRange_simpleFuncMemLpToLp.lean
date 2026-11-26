-- Prove2me | Theorems.Thm_Auto_aux_denseRange_simpleFuncMemLpToLp
-- name    : Auto.aux_denseRange_simpleFuncMemLpToLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:50.064973+00:00
-- url     : https://prove2.me/theorems/2678d362-004f-5a11-ab6b-038f5acc086a
-- title:
--   Auto: aux dense Range simple Func Mem Lp To Lp
-- statement:
--   The integrable simple-function core is dense in the ambient `Lp` space.  This is used
--   to transfer endpoint estimates from the core on which a raw operator is defined.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8857-L8866
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8857-L8866

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

theorem Auto.aux_denseRange_simpleFuncMemLpToLp {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    DenseRange (aux_simpleFuncMemLpToLp p μ) := by sorry
