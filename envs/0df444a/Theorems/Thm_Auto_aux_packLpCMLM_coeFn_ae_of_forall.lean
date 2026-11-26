-- Prove2me | Theorems.Thm_Auto_aux_packLpCMLM_coeFn_ae_of_forall
-- name    : Auto.aux_packLpCMLM_coeFn_ae_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:19.09681+00:00
-- url     : https://prove2.me/theorems/622ed1f3-ada7-49bb-8946-5cdc4698a4e7
-- title:
--   Auto: aux pack Lp CMLM coe Fn ae of forall
-- statement:
--   The Auto construction uses the aux pack Lp CMLM coe Fn ae of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9444-L9455
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9444-L9455

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

theorem Auto.aux_packLpCMLM_coeFn_ae_of_forall {J : ℕ} {ι Y : Type*} {X : ι → Type*}
    [Fintype ι] [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
    (B : Fin J → ContinuousMultilinearMap ℂ X (Lp ℂ 2 μ)) (x : ∀ i, X i)
    (raw : Fin J → Y → ℂ) (hraw : ∀ j, (B j x : Y → ℂ) =ᵐ[μ] raw j) :
    ((aux_packLpCMLM B x : Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) :
      Fin J × Y → ℂ) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ raw z.1 z.2 := by sorry
