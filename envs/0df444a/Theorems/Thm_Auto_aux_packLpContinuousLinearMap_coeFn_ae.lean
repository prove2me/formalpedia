-- Prove2me | Theorems.Thm_Auto_aux_packLpContinuousLinearMap_coeFn_ae
-- name    : Auto.aux_packLpContinuousLinearMap_coeFn_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:56.891873+00:00
-- url     : https://prove2.me/theorems/590cbed0-3c2a-413c-9946-e44a3b047ffb
-- title:
--   Auto: aux pack Lp Continuous Linear Map coe Fn ae
-- statement:
--   The Auto construction uses the aux pack Lp Continuous Linear Map coe Fn ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9373-L9383
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9373-L9383

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

theorem Auto.aux_packLpContinuousLinearMap_coeFn_ae {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ]
    (u : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ)) :
    ((aux_packLpContinuousLinearMap (μ := μ) u :
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) : Fin J × X → ℂ) =ᵐ[
        (Measure.count : Measure (Fin J)).prod μ]
      aux_packLpFun (fun j ↦ u j) := by sorry
