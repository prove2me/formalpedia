-- Prove2me | Theorems.Thm_Auto_aux_extendLpCMLMToSimpleFuncIntegrable_apply_of_integrable
-- name    : Auto.aux_extendLpCMLMToSimpleFuncIntegrable_apply_of_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:05.680299+00:00
-- url     : https://prove2.me/theorems/ad545d47-875d-5149-bcb3-dff09803447b
-- title:
--   Auto: aux extend Lp CMLMTo Simple Func Integrable apply of integrable
-- statement:
--   The common-core totalization agrees with the original continuous multilinear map on
--   integrable simple-function inputs.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8701-L8723
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8701-L8723

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

theorem Auto.aux_extendLpCMLMToSimpleFuncIntegrable_apply_of_integrable {ι X F : Type*}
    [Fintype ι] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (f : ∀ _i, SimpleFunc X ℂ)
    (hf : ∀ i, Integrable (f i : X → ℂ) μ) :
    aux_extendLpCMLMToSimpleFuncIntegrable p μ hp_top B f =
      B fun i ↦ ((SimpleFunc.memLp_iff_integrable
        (aux_simpleFuncExponent_ne_zero (p := p i)) (hp_top i)).mpr
        (hf i)).toLp (f i) := by sorry
