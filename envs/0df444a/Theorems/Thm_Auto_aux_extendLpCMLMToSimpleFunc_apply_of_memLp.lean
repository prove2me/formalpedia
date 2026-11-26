-- Prove2me | Theorems.Thm_Auto_aux_extendLpCMLMToSimpleFunc_apply_of_memLp
-- name    : Auto.aux_extendLpCMLMToSimpleFunc_apply_of_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:51.325739+00:00
-- url     : https://prove2.me/theorems/eeeb8d7e-28da-5153-be81-0c2e1be70c49
-- title:
--   Auto: aux extend Lp CMLMTo Simple Func apply of mem Lp
-- statement:
--   The total simple-function extension agrees with the original `Lp` map on its core.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8610-L8626
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8610-L8626

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

theorem Auto.aux_extendLpCMLMToSimpleFunc_apply_of_memLp {ι X F : Type*}
    [Fintype ι] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (f : ∀ _i : ι, SimpleFunc X ℂ)
    (hf : ∀ i, MemLp (f i : X → ℂ) (p i) μ) :
    aux_extendLpCMLMToSimpleFunc p μ B f =
      B fun i ↦ (hf i).toLp (f i) := by sorry
