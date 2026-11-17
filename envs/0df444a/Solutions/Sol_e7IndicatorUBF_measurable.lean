-- Prove2me | solution 1 for e7IndicatorUBF_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:35:53.1812+00:00
-- url     : https://prove2.me/submissions/5995545b-4253-430a-828a-eabf2d3f9ff0

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
import Definitions.Def_e7IndicatorUBF
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7IndicatorUBF_measurable {E : Type*} [MeasurableSpace E]
    (s : Set E) (hs : MeasurableSet s) :
    Measurable (e7IndicatorUBF s : E → ℝ) := by
  show Measurable (fun x => if x ∈ s then (1 : ℝ) else 0)
  exact Measurable.ite hs measurable_const measurable_const

theorem solution {E : Type*} [MeasurableSpace E]
    (s : Set E) (hs : MeasurableSet s) :
    Measurable (e7IndicatorUBF s : E → ℝ) := by
  show Measurable (fun x => if x ∈ s then (1 : ℝ) else 0)
  exact Measurable.ite hs measurable_const measurable_const


