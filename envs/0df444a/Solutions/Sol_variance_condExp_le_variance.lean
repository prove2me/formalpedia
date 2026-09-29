-- Prove2me | solution 1 for variance_condExp_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:30:13.971789+00:00
-- url     : https://prove2.me/submissions/0167f78f-1529-45a8-8969-a9c93f03139f

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[μ[X | m]; μ] ≤ Var[X; μ] := by
  have hkey : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] :=
    integral_condVar_add_variance_condExp hm hX
  have hcv_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] Var[X; μ | m] := by
    have hsq : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => (X ω - (μ[X | m]) ω) ^ 2) :=
      Filter.Eventually.of_forall (fun ω => sq_nonneg _)
    exact condExp_nonneg hsq
  have hnn : 0 ≤ μ[Var[X; μ | m]] := integral_nonneg_of_ae hcv_nonneg
  linarith
