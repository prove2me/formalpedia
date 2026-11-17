-- Prove2me | solution 1 for e7_triangular_bump_support_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:35:51.333018+00:00
-- url     : https://prove2.me/submissions/6239283f-c661-486f-a531-38dc18e041d6

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
import Definitions.Def_e7_triangular_bump
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_triangular_bump_support_subset_closedBall (x₀ ε : ℝ) (hε : 0 < ε) :
    Function.support (e7_triangular_bump x₀ ε) ⊆ Metric.closedBall x₀ ε := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, Real.dist_eq]
  by_contra h
  push_neg at h
  apply hx
  unfold e7_triangular_bump
  have h1 : 1 ≤ |x - x₀| / ε := (one_le_div hε).2 h.le
  exact max_eq_left (by linarith)

theorem solution (x₀ ε : ℝ) (hε : 0 < ε) :
    Function.support (e7_triangular_bump x₀ ε) ⊆ Metric.closedBall x₀ ε := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, Real.dist_eq]
  by_contra h
  push_neg at h
  apply hx
  unfold e7_triangular_bump
  have h1 : 1 ≤ |x - x₀| / ε := (one_le_div hε).2 h.le
  exact max_eq_left (by linarith)


