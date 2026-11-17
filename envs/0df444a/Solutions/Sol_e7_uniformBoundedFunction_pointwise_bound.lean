-- Prove2me | solution 1 for e7_uniformBoundedFunction_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:38:59.880081+00:00
-- url     : https://prove2.me/submissions/8830448f-9be4-4f5a-a5b8-33a026322b33

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

theorem e7_uniformBoundedFunction_pointwise_bound
    {E : Type*} [MeasurableSpace E] (f : UniformBoundedFunction E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(f : E → ℝ) x‖ ≤ M := by
  exact ⟨‖f‖, norm_nonneg _, fun x => lp.norm_apply_le_norm ENNReal.top_ne_zero f x⟩

theorem solution
    {E : Type*} [MeasurableSpace E] (f : UniformBoundedFunction E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(f : E → ℝ) x‖ ≤ M := by
  exact ⟨‖f‖, norm_nonneg _, fun x => lp.norm_apply_le_norm ENNReal.top_ne_zero f x⟩


