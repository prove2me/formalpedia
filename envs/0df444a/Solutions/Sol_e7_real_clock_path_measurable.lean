-- Prove2me | solution 1 for e7_real_clock_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:39:00.779403+00:00
-- url     : https://prove2.me/submissions/c23bd59e-6f00-4451-9f5d-10f3608d16ec

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

theorem e7_real_clock_path_measurable
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (g : E → ℝ)
    (hX : Measurable (Function.uncurry X)) (hg : Measurable g)
    (hclock : Measurable (fun z : ℝ × Ω => (z.1.toNNReal, z.2))) :
    Measurable (Function.uncurry (fun (w : ℝ) (ω : Ω) => g (X w.toNNReal ω))) := by
  exact hg.comp (hX.comp hclock)

theorem solution
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (g : E → ℝ)
    (hX : Measurable (Function.uncurry X)) (hg : Measurable g)
    (hclock : Measurable (fun z : ℝ × Ω => (z.1.toNNReal, z.2))) :
    Measurable (Function.uncurry (fun (w : ℝ) (ω : Ω) => g (X w.toNNReal ω))) := by
  exact hg.comp (hX.comp hclock)


