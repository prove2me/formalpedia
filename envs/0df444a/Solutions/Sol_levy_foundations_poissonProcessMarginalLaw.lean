-- Prove2me | solution 1 for levy_foundations_poissonProcessMarginalLaw
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:20.31578+00:00
-- url     : https://prove2.me/submissions/86c8f75f-cbea-49f7-8d96-24f094f20e84

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
    (t : ℝ≥0) : μ.map (N t) = poissonMeasure (rate * t) := by
  have := h.increment_poisson 0 t
  have h0 := h.start_zero
  simpa [h0] using this
