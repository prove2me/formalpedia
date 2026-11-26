-- Prove2me | Theorems.Thm_Auto_aux_ContinuousMultilinearMap_norm_sq_le_of_denseRange
-- name    : Auto.aux_ContinuousMultilinearMap_norm_sq_le_of_denseRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:20.492799+00:00
-- url     : https://prove2.me/theorems/9cc635ef-2a39-4f04-a79b-59d08a892376
-- title:
--   Auto: aux Continuous Multilinear Map norm sq le of dense Range
-- statement:
--   The squared form of `aux_ContinuousMultilinearMap_norm_le_of_denseRange`, useful for
--   finite `L²` energies whose natural endpoint bounds contain squared norms.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8826-L8851
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8826-L8851

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

theorem Auto.aux_ContinuousMultilinearMap_norm_sq_le_of_denseRange
    {𝕜 ι F : Type*} {E₀ E : ι → Type*}
    [NontriviallyNormedField 𝕜] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (E₀ i)] [∀ i, NormedSpace 𝕜 (E₀ i)]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (B : ContinuousMultilinearMap 𝕜 E F)
    (e : ∀ i, E₀ i →L[𝕜] E i) (he : ∀ i, DenseRange (e i))
    (C : ℝ)
    (hbound : ∀ x : ∀ i, E₀ i,
      ‖B (fun i ↦ e i (x i))‖ ^ 2 ≤ C * ∏ i, ‖e i (x i)‖ ^ 2) :
    ∀ x : ∀ i, E i, ‖B x‖ ^ 2 ≤ C * ∏ i, ‖x i‖ ^ 2 := by sorry
