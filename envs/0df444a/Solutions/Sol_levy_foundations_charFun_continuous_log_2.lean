-- Prove2me | solution 2 for levy_foundations_charFun_continuous_log
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:12:17.511503+00:00
-- url     : https://prove2.me/submissions/0bad047a-0aba-4b3f-8ae3-61a5e2f16fc7

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory


theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hne : ∀ ξ : ℝ, charFun μ ξ ≠ 0) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧ ψ 0 = 0 ∧
        ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ) := by
  have hc : Continuous (charFun μ) := continuous_charFun
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (A := ℝ) (f := ⟨charFun μ, hc⟩) (a₀ := 0) (e₀ := 0) (by simp) (fun a => hne a)
  refine ⟨F, F.continuous, hF0, fun ξ => ?_⟩
  have := congrFun hF ξ
  simpa using this.symm
