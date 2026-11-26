-- Prove2me | Theorems.Thm_Auto_aux_ContinuousMultilinearMap_norm_le_of_denseRange
-- name    : Auto.aux_ContinuousMultilinearMap_norm_le_of_denseRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:28.248131+00:00
-- url     : https://prove2.me/theorems/1b65aaa1-f505-4123-89d6-b92678d980d2
-- title:
--   Auto: aux Continuous Multilinear Map norm le of dense Range
-- statement:
--   A product-norm estimate for a continuous multilinear map extends from a coordinatewise
--   dense core to all inputs.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8795-L8820
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8795-L8820

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

theorem Auto.aux_ContinuousMultilinearMap_norm_le_of_denseRange
    {𝕜 ι F : Type*} {E₀ E : ι → Type*}
    [NontriviallyNormedField 𝕜] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (E₀ i)] [∀ i, NormedSpace 𝕜 (E₀ i)]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (B : ContinuousMultilinearMap 𝕜 E F)
    (e : ∀ i, E₀ i →L[𝕜] E i) (he : ∀ i, DenseRange (e i))
    (C : ℝ)
    (hbound : ∀ x : ∀ i, E₀ i,
      ‖B (fun i ↦ e i (x i))‖ ≤ C * ∏ i, ‖e i (x i)‖) :
    ∀ x : ∀ i, E i, ‖B x‖ ≤ C * ∏ i, ‖x i‖ := by sorry
