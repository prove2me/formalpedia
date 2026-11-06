-- Prove2me | Theorems.Thm_EthierKurtz_martingale_solution_is_markov
-- name    : EthierKurtz.martingale_solution_is_markov
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T12:51:23.616062+00:00
-- url     : https://prove2.me/theorems/54176b4e-57f4-462c-805f-6a16a9a0aec1
-- title:
--   The martingale solution is Markov relative to its process past
-- statement:
--   Under the separating hypothesis on L, the conditional expectation of every measurable bounded observable given the full process past agrees with conditioning on the present state.

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

theorem EthierKurtz.martingale_solution_is_markov

    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MetricSpace E] [BorelSpace E]
    [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)

    :
    ∀ (s t : ℝ≥0) (f : UniformBoundedFunction E),
      Measurable (f : E → ℝ) →
      P[fun ω => f (X (s + t) ω) | processPast X s] =ᵐ[P]
        P[fun ω => f (X (s + t) ω) |
          MeasurableSpace.comap (X s) ‹MeasurableSpace E›] := by sorry
