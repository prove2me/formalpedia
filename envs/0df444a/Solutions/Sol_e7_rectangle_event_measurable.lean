-- Prove2me | solution 1 for e7_rectangle_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:38:58.129596+00:00
-- url     : https://prove2.me/submissions/66c41a3d-8f18-46e1-9da5-74151225fab5

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
import Definitions.Def_e7_rectangle_event
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_rectangle_event_measurable
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (hXmeas : Measurable (Function.uncurry X))
    (n : ℕ) (r : Fin n → ℝ≥0) (B : Fin n → Set E)
    (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet (e7_rectangle_event X n r B) := by
  have hm : ∀ i, Measurable (X (r i)) := fun i =>
    hXmeas.comp (measurable_const.prodMk measurable_id)
  have : e7_rectangle_event X n r B = ⋂ i, X (r i) ⁻¹' B i := by
    ext ω; simp [e7_rectangle_event]
  rw [this]
  exact MeasurableSet.iInter (fun i => hm i (hB i))

theorem solution
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (hXmeas : Measurable (Function.uncurry X))
    (n : ℕ) (r : Fin n → ℝ≥0) (B : Fin n → Set E)
    (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet (e7_rectangle_event X n r B) := by
  have hm : ∀ i, Measurable (X (r i)) := fun i =>
    hXmeas.comp (measurable_const.prodMk measurable_id)
  have : e7_rectangle_event X n r B = ⋂ i, X (r i) ⁻¹' B i := by
    ext ω; simp [e7_rectangle_event]
  rw [this]
  exact MeasurableSet.iInter (fun i => hm i (hB i))


