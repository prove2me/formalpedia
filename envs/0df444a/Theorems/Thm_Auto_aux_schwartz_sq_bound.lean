-- Prove2me | Theorems.Thm_Auto_aux_schwartz_sq_bound
-- name    : Auto.aux_schwartz_sq_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:05.772716+00:00
-- url     : https://prove2.me/theorems/8e1171d2-5ba2-5afd-93a4-11395b320cc2
-- title:
--   Auto: aux schwartz sq bound
-- statement:
--   A sharp squared norm estimate for a complex CMLM transfers from Schwartz inputs to
--   arbitrary `Lp` inputs.  Its codomain is arbitrary, so it applies to packed `L²` targets.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8973-L9009
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8973-L9009

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

theorem Auto.aux_schwartz_sq_bound
    {ι X F : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
    [SecondCountableTopologyEither X ℂ]
    {μ : Measure X} [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) [∀ i, Fact (1 ≤ p i)]
    (hpfin : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (K : ℝ)
    (hcore : ∀ f : ι → SchwartzMap X ℂ,
      ‖B.toMultilinearMap (fun i ↦ (f i).toLp (p i) μ)‖ ^ 2 ≤
        K * ∏ i, ‖(f i).toLp (p i) μ‖ ^ 2) :
    ∀ g : (i : ι) → Lp ℂ (p i) μ,
      ‖B.toMultilinearMap g‖ ^ 2 ≤ K * ∏ i, ‖g i‖ ^ 2 := by sorry
