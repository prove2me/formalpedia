-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_sq_packLpContinuousLinearMap
-- name    : Auto.aux_eLpNorm_sq_packLpContinuousLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:03.218171+00:00
-- url     : https://prove2.me/theorems/e08ceaab-8774-5644-9b71-1358838e6ec7
-- title:
--   Auto: aux e Lp Norm sq pack Lp Continuous Linear Map
-- statement:
--   The Auto construction uses the aux e Lp Norm sq pack Lp Continuous Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9385-L9394
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9385-L9394

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

theorem Auto.aux_eLpNorm_sq_packLpContinuousLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ]
    (u : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ)) :
    eLpNorm ((aux_packLpContinuousLinearMap (μ := μ) u :
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) : Fin J × X → ℂ) 2
        ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 := by sorry
