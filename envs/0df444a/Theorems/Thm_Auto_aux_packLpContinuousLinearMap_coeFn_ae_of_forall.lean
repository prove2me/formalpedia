-- Prove2me | Theorems.Thm_Auto_aux_packLpContinuousLinearMap_coeFn_ae_of_forall
-- name    : Auto.aux_packLpContinuousLinearMap_coeFn_ae_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:06.872328+00:00
-- url     : https://prove2.me/theorems/7ba615b2-f340-557d-8ef4-3745de93f085
-- title:
--   Auto: aux pack Lp Continuous Linear Map coe Fn ae of forall
-- statement:
--   The Auto construction uses the aux pack Lp Continuous Linear Map coe Fn ae of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9396-L9406
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9396-L9406

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

theorem Auto.aux_packLpContinuousLinearMap_coeFn_ae_of_forall {J : ℕ} {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ)) (raw : Fin J → X → ℂ)
    (hraw : ∀ j, (u j : X → ℂ) =ᵐ[μ] raw j) :
    ((aux_packLpContinuousLinearMap (μ := μ) u :
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) : Fin J × X → ℂ) =ᵐ[
        (Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ raw z.1 z.2 := by sorry
