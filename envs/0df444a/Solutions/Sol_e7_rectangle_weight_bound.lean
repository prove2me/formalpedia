-- Prove2me | solution 1 for e7_rectangle_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:38:58.993617+00:00
-- url     : https://prove2.me/submissions/1bf147c9-9b0b-4213-b882-e8b8adf23942

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

theorem e7_rectangle_weight_bound
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (n : ℕ) (r : Fin n → ℝ≥0)
    (B : Fin n → Set E) :
    ∀ ω, ‖∏ i, e7IndicatorUBF (B i) (X (r i) ω)‖ ≤ (1 : ℝ) := by
  intro ω
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  show ‖(if X (r i) ω ∈ B i then (1 : ℝ) else 0)‖ ≤ 1
  split_ifs <;> simp

theorem solution
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → E) (n : ℕ) (r : Fin n → ℝ≥0)
    (B : Fin n → Set E) :
    ∀ ω, ‖∏ i, e7IndicatorUBF (B i) (X (r i) ω)‖ ≤ (1 : ℝ) := by
  intro ω
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  show ‖(if X (r i) ω ∈ B i then (1 : ℝ) else 0)‖ ≤ 1
  split_ifs <;> simp


