-- Prove2me | solution 1 for variance_nested_two_step
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:30:14.257624+00:00
-- url     : https://prove2.me/submissions/ed0a9d03-fa50-48c8-9ed3-d795287961fe

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) {m' : MeasurableSpace Ω} (hm' : m' ≤ m)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = μ[Var[X; μ | m]] + μ[Var[μ[X | m]; μ | m']] + Var[μ[X | m']; μ] := by
  have hm'0 : m' ≤ m₀ := le_trans hm' hm
  have h1 : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] :=
    integral_condVar_add_variance_condExp hm hX
  have hY : MemLp (μ[X | m]) 2 μ := hX.condExp one_le_two
  have h2 : μ[Var[μ[X | m]; μ | m']] + Var[μ[μ[X | m] | m']; μ] = Var[μ[X | m]; μ] :=
    integral_condVar_add_variance_condExp hm'0 hY
  have htower : μ[μ[X | m] | m'] =ᵐ[μ] μ[X | m'] := condExp_condExp_of_le hm' hm
  have htv : Var[μ[μ[X | m] | m']; μ] = Var[μ[X | m']; μ] := variance_congr htower
  rw [htv] at h2
  linarith
