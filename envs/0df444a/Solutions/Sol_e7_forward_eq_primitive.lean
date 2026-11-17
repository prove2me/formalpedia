-- Prove2me | solution 1 for e7_forward_eq_primitive
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:38:57.287066+00:00
-- url     : https://prove2.me/submissions/bf9570d9-3303-41fb-a79a-446615b7b1fa

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
import Definitions.Def_e7_forward_primitive
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_forward_eq_primitive (qf qg : ℝ → ℝ)
    (hweak : ∀ t, 0 ≤ t →
      qf t - qf 0 = ∫ s in (0 : ℝ)..t, qg s) :
    ∀ t, 0 ≤ t → qf t = e7_forward_primitive (qf 0) qg t := by
  intro t ht
  unfold e7_forward_primitive
  linarith [hweak t ht]

theorem solution (qf qg : ℝ → ℝ)
    (hweak : ∀ t, 0 ≤ t →
      qf t - qf 0 = ∫ s in (0 : ℝ)..t, qg s) :
    ∀ t, 0 ≤ t → qf t = e7_forward_primitive (qf 0) qg t := by
  intro t ht
  unfold e7_forward_primitive
  linarith [hweak t ht]


