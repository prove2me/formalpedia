-- Prove2me | Theorems.Thm_Auto_aux_integrableSimpleFuncToLp_apply
-- name    : Auto.aux_integrableSimpleFuncToLp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:39.312836+00:00
-- url     : https://prove2.me/theorems/624d085b-baa9-4d11-a4e6-4ce1dd1c6067
-- title:
--   Auto: aux integrable Simple Func To Lp apply
-- statement:
--   The common-core-to-`Lp` map is the ordinary quotient map on integrable simple functions.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8673-L8679
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8673-L8679

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

theorem Auto.aux_integrableSimpleFuncToLp_apply {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (f : SimpleFunc X ℂ) (hf : Integrable (f : X → ℂ) μ) :
    aux_integrableSimpleFuncToLp p μ hp_top ⟨f, memLp_one_iff_integrable.mpr hf⟩ =
      ((SimpleFunc.memLp_iff_integrable
        (aux_simpleFuncExponent_ne_zero (p := p)) hp_top).mpr hf).toLp f := by sorry
