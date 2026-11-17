-- Prove2me | solution 1 for targetResolvent_range
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:42:58.260841+00:00
-- url     : https://prove2.me/submissions/ec164183-9eb3-4533-a2da-490d7d364f95

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
import Definitions.Def_targetResolventRaw
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

section TargetMaps
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
theorem targetResolvent_range (A' : Submodule ℝ (U × U)) (a : ℝ) :
    Set.range (targetResolventRaw A' a) =
      (fun fg : U × U => a • fg.1 - fg.2) '' (A' : Set (U × U)) := by
  ext y
  simp [targetResolventRaw]

theorem solution (A' : Submodule ℝ (U × U)) (a : ℝ) :
    Set.range (targetResolventRaw A' a) =
      (fun fg : U × U => a • fg.1 - fg.2) '' (A' : Set (U × U)) := by
  ext y
  simp [targetResolventRaw]

end TargetMaps

