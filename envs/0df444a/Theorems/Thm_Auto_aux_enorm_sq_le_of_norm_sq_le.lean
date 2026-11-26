-- Prove2me | Theorems.Thm_Auto_aux_enorm_sq_le_of_norm_sq_le
-- name    : Auto.aux_enorm_sq_le_of_norm_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:50.137977+00:00
-- url     : https://prove2.me/theorems/d7ba6494-d6db-5910-a7f0-5f245d8ad9aa
-- title:
--   Auto: aux enorm sq le of norm sq le
-- statement:
--   Converts a real squared product-norm estimate to its extended-norm form.
--   This is used to pass sharp continuous-multilinear endpoint estimates into
--   the squared `Lp` interpolation theorem.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8926-L8942
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8926-L8942

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

theorem Auto.aux_enorm_sq_le_of_norm_sq_le
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (K : ℝ) (hK : 0 ≤ K) (y : F) (x : ∀ i, E i)
    (h : ‖y‖ ^ 2 ≤ K * ∏ i, ‖x i‖ ^ 2) :
    ‖y‖ₑ ^ 2 ≤ ENNReal.ofReal K * ∏ i, ‖x i‖ₑ ^ 2 := by sorry
