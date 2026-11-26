-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_sq_packLpCMLM_eq_sum_raw
-- name    : Auto.aux_eLpNorm_sq_packLpCMLM_eq_sum_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:22.979525+00:00
-- url     : https://prove2.me/theorems/66e54351-e913-4a7e-a253-482860c40cef
-- title:
--   Auto: aux e Lp Norm sq pack Lp CMLM eq sum raw
-- statement:
--   The Auto construction uses the aux e Lp Norm sq pack Lp CMLM eq sum raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9457-L9468
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9457-L9468

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

theorem Auto.aux_eLpNorm_sq_packLpCMLM_eq_sum_raw {J : ℕ} {ι Y : Type*} {X : ι → Type*}
    [Fintype ι] [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
    (B : Fin J → ContinuousMultilinearMap ℂ X (Lp ℂ 2 μ)) (x : ∀ i, X i)
    (raw : Fin J → Y → ℂ) (hraw : ∀ j, (B j x : Y → ℂ) =ᵐ[μ] raw j) :
    eLpNorm ((aux_packLpCMLM B x : Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) :
      Fin J × Y → ℂ) 2 ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (raw j) 2 μ ^ 2 := by sorry
