-- Prove2me | solution 1 for denseRange_codRestrict_of_closure_range
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:35:56.755495+00:00
-- url     : https://prove2.me/submissions/91d37be3-7bb3-4148-9275-251843578332

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem denseRange_codRestrict_of_closure_range
    {D U : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : Submodule ℝ U) (f : D →ₗ[ℝ] U)
    (hmem : ∀ x, f x ∈ L)
    (hclose : closure (Set.range f) = (L : Set U)) :
    DenseRange (LinearMap.codRestrict L f hmem) := by
  have hr : Set.range f = Subtype.val '' Set.range (LinearMap.codRestrict L f hmem) := by
    rw [← Set.range_comp]
    rfl
  intro x
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have hx : (x : U) ∈ closure (Set.range f) := by rw [hclose]; exact x.2
  rw [hr] at hx
  exact hx

theorem solution
    {D U : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : Submodule ℝ U) (f : D →ₗ[ℝ] U)
    (hmem : ∀ x, f x ∈ L)
    (hclose : closure (Set.range f) = (L : Set U)) :
    DenseRange (LinearMap.codRestrict L f hmem) := by
  have hr : Set.range f = Subtype.val '' Set.range (LinearMap.codRestrict L f hmem) := by
    rw [← Set.range_comp]
    rfl
  intro x
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have hx : (x : U) ∈ closure (Set.range f) := by rw [hclose]; exact x.2
  rw [hr] at hx
  exact hx


