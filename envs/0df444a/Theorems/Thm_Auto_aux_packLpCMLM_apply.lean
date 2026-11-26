-- Prove2me | Theorems.Thm_Auto_aux_packLpCMLM_apply
-- name    : Auto.aux_packLpCMLM_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:24.691052+00:00
-- url     : https://prove2.me/theorems/763cf504-6aa3-5fba-9a7d-78fa335eff95
-- title:
--   Auto: aux pack Lp CMLM apply
-- statement:
--   The Auto construction uses the aux pack Lp CMLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9436-L9442
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9436-L9442

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

theorem Auto.aux_packLpCMLM_apply {J : ℕ} {ι Y : Type*} {X : ι → Type*} [Fintype ι]
    [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
    (B : Fin J → ContinuousMultilinearMap ℂ X (Lp ℂ 2 μ)) (x : ∀ i, X i) :
    aux_packLpCMLM B x = aux_packLpContinuousLinearMap (μ := μ)
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin J ↦ Lp ℂ 2 μ)).symm
        (fun j ↦ B j x)) := by sorry

attribute [defeq] Auto.aux_packLpCMLM_apply
