-- Prove2me | solution 1 for e7_time_tuple_has_largest_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:57:49.884744+00:00
-- url     : https://prove2.me/submissions/fe693a91-fee9-4c74-ac8c-dfad86c18da8

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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical
theorem solution (n : ℕ)
    (t : Fin (n + 1) → ℝ≥0) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      ∀ i : Fin n, t (σ i.castSucc) ≤ t (σ (Fin.last n)) := by
  classical
  obtain ⟨j, hj, hmax⟩ := Set.exists_max_image
    (Set.univ : Set (Fin (n + 1))) t Set.finite_univ
    ⟨Fin.last n, Set.mem_univ _⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j (Fin.last n)
  refine ⟨σ, ?_⟩
  intro i
  calc
    t (σ i.castSucc) ≤ t j := hmax _ (Set.mem_univ _)
    _ = t (σ (Fin.last n)) := by simp [σ]
