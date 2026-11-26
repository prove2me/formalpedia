-- Prove2me | Theorems.Thm_Auto_aux_integrableSimpleFuncRetract_apply_of_integrable
-- name    : Auto.aux_integrableSimpleFuncRetract_apply_of_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:19.411122+00:00
-- url     : https://prove2.me/theorems/7323dff7-31cd-44d8-b2f8-6b12ddfc7b67
-- title:
--   Auto: aux integrable Simple Func Retract apply of integrable
-- statement:
--   The common-core retraction is the identity on every integrable simple function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8643-L8646
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8643-L8646

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

theorem Auto.aux_integrableSimpleFuncRetract_apply_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : SimpleFunc X ℂ) (hf : Integrable (f : X → ℂ) μ) :
    aux_integrableSimpleFuncRetract μ f = ⟨f, (memLp_one_iff_integrable.mpr hf)⟩ := by sorry
