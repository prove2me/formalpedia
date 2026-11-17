-- Prove2me | solution 1 for e7_triangular_bump_continuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:35:50.377355+00:00
-- url     : https://prove2.me/submissions/2fadc899-3104-44e7-a1d4-df0d61821d8a

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

theorem e7_triangular_bump_continuous (x₀ ε : ℝ) : 0 < ε →
    Continuous (e7_triangular_bump x₀ ε) := by
  intro _
  unfold e7_triangular_bump
  exact continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const ε))

theorem solution (x₀ ε : ℝ) : 0 < ε →
    Continuous (e7_triangular_bump x₀ ε) := by
  intro _
  unfold e7_triangular_bump
  exact continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const ε))


