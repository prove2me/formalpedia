-- Prove2me | solution 1 for e7_empty_past_initial_L_integrals_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T14:58:27.024537+00:00
-- url     : https://prove2.me/submissions/c73d4a46-dd5e-4d53-b957-32599848857a

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

theorem e7_empty_past_initial_L_integrals_eq
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω']
    (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) (Q : Measure Ω')
    (X : ℝ≥0 → Ω → E) (Y : ℝ≥0 → Ω' → E)
    (hX : SolvesMartingaleProblem A μ P X)
    (hY : SolvesMartingaleProblem A μ Q Y)
    (f : UniformBoundedFunction E) :
    (∫ x, (f : E → ℝ) x ∂Measure.map (fun ω => X 0 ω) P) =
      ∫ x, (f : E → ℝ) x ∂Measure.map (fun ω => Y 0 ω) Q := by
  change (∫ x, (f : E → ℝ) x ∂Measure.map (X 0) P) = ∫ x, (f : E → ℝ) x ∂Measure.map (Y 0) Q
  rw [hX.2.1, hY.2.1]

theorem solution
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω']
    (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) (Q : Measure Ω')
    (X : ℝ≥0 → Ω → E) (Y : ℝ≥0 → Ω' → E)
    (hX : SolvesMartingaleProblem A μ P X)
    (hY : SolvesMartingaleProblem A μ Q Y)
    (f : UniformBoundedFunction E) :
    (∫ x, (f : E → ℝ) x ∂Measure.map (fun ω => X 0 ω) P) =
      ∫ x, (f : E → ℝ) x ∂Measure.map (fun ω => Y 0 ω) Q := by
  change (∫ x, (f : E → ℝ) x ∂Measure.map (X 0) P) = ∫ x, (f : E → ℝ) x ∂Measure.map (Y 0) Q
  rw [hX.2.1, hY.2.1]


