-- Prove2me | solution 1 for expected_condVar_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:30:13.64836+00:00
-- url     : https://prove2.me/submissions/b74538f6-305e-4900-90bd-58f5e03433fd

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    μ[Var[X; μ | m]] ≤ Var[X; μ] := by
  have hkey : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] :=
    integral_condVar_add_variance_condExp hm hX
  have hnn : 0 ≤ Var[μ[X | m]; μ] := variance_nonneg _ _
  linarith
