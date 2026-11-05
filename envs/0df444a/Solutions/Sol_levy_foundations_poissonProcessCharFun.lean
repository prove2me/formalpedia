-- Prove2me | solution 1 for levy_foundations_poissonProcessCharFun
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:21.220021+00:00
-- url     : https://prove2.me/submissions/9085bfae-8163-4243-8206-6432250d164a

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPoissonProcess
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : LevyFoundations.IsPoissonProcess N rate μ)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
      Complex.exp (↑(rate * t : ℝ≥0) * (Complex.exp (↑ξ * Complex.I) - 1)) := by
  have hlaw : μ.map (N t) = poissonMeasure (rate * t) := by
    have := h.increment_poisson 0 t
    have h0 := h.start_zero
    simpa [h0] using this
  have hm : AEMeasurable (N t) μ := by
    by_contra hc
    rw [Measure.map_of_not_aemeasurable hc] at hlaw
    have : IsProbabilityMeasure (poissonMeasure (rate * t)) := inferInstance
    have h1 := this.measure_univ
    rw [← hlaw] at h1
    simp at h1
  have : μ.map (fun ω => (N t ω : ℝ)) = (μ.map (N t)).map (Nat.cast : ℕ → ℝ) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
    rfl
  rw [this, hlaw, charFun_map_cast_poissonMeasure]
