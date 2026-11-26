-- Prove2me | Theorems.Thm_Auto_aux_extendLpCMLMToSimpleFuncIntegrable_enorm_eq_zero_of_eLpNorm_eq_zero
-- name    : Auto.aux_extendLpCMLMToSimpleFuncIntegrable_enorm_eq_zero_of_eLpNorm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:22.767107+00:00
-- url     : https://prove2.me/theorems/33cb42a8-ef35-43ca-93a9-7c59c8d221df
-- title:
--   Auto: aux extend Lp CMLMTo Simple Func Integrable enorm eq zero of e Lp Norm eq zero
-- statement:
--   The common-integrable-core totalization vanishes when any finite-`Lᵖ`
--   input has zero extended norm.  This supplies the null-input compatibility
--   required by `multilinear_interpolation_convexHull_Lp_sq`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8760-L8772
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8760-L8772

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

theorem Auto.aux_extendLpCMLMToSimpleFuncIntegrable_enorm_eq_zero_of_eLpNorm_eq_zero
    {m : ℕ} {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : Fin (m + 1) → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (u : Fin (m + 1) → ℝ) (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1))
    (hzero : eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0) :
    ‖aux_extendLpCMLMToSimpleFuncIntegrable p μ hp_top B g‖ₑ = 0 := by sorry
