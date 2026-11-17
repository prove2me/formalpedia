-- Prove2me | solution 1 for e7_measurable_of_dense_first_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T14:58:55.986408+00:00
-- url     : https://prove2.me/submissions/2f1e8c80-af21-4a96-bc2a-41ec738c2785

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

theorem e7_measurable_of_dense_first_coordinates
    {E : Type*} [MeasurableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hsub : A' ≤ A)
    (hAmeas : ∀ fg ∈ A,
      Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hclose : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E))) :
    ∀ f : L, Measurable (f.val : E → ℝ) := by
  intro f
  have hf : (f.val : UniformBoundedFunction E) ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) := by
    rw [hclose]; exact f.2
  obtain ⟨g, hgmem, hgt⟩ := mem_closure_iff_seq_limit.mp hf
  have hgm : ∀ n, Measurable ((g n : UniformBoundedFunction E) : E → ℝ) := by
    intro n
    obtain ⟨fg, hfg, hfe⟩ := hgmem n
    rw [← hfe]
    exact (hAmeas fg (hsub hfg)).1
  refine measurable_of_tendsto_metrizable hgm ?_
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero] at hgt ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgt
  have := lp.norm_apply_le_norm (p := ∞) (by simp) (g n - f.val) x
  simpa [lp.coeFn_sub] using this

theorem solution
    {E : Type*} [MeasurableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hsub : A' ≤ A)
    (hAmeas : ∀ fg ∈ A,
      Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hclose : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E))) :
    ∀ f : L, Measurable (f.val : E → ℝ) := by
  intro f
  have hf : (f.val : UniformBoundedFunction E) ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) := by
    rw [hclose]; exact f.2
  obtain ⟨g, hgmem, hgt⟩ := mem_closure_iff_seq_limit.mp hf
  have hgm : ∀ n, Measurable ((g n : UniformBoundedFunction E) : E → ℝ) := by
    intro n
    obtain ⟨fg, hfg, hfe⟩ := hgmem n
    rw [← hfe]
    exact (hAmeas fg (hsub hfg)).1
  refine measurable_of_tendsto_metrizable hgm ?_
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero] at hgt ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgt
  have := lp.norm_apply_le_norm (p := ∞) (by simp) (g n - f.val) x
  simpa [lp.coeFn_sub] using this


