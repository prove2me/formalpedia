-- Prove2me | solution 1 for levy_foundations_charFun_continuous_log
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:06:26.789737+00:00
-- url     : https://prove2.me/submissions/6030df57-6f1a-4b2f-8ae9-c160d807f28d

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology

/-- A nonzero real characteristic function admits a continuous logarithm,
normalised at the origin, by lifting through the exponential covering map. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hne : ∀ ξ : ℝ, charFun μ ξ ≠ 0) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧ ψ 0 = 0 ∧
        ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ) := by
  have hcont : Continuous (charFun μ) :=
    MeasureTheory.continuous_charFun
  have hφ0 : charFun μ 0 = 1 := by
    simp [charFun_zero, Measure.real, measure_univ]
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by
    simp [f, hφ0]
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) :=
    fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  exact ⟨F, F.continuous, hF0, fun ξ => by
    have h := congr_fun hFexp ξ
    simp [Function.comp] at h
    exact h.symm⟩
