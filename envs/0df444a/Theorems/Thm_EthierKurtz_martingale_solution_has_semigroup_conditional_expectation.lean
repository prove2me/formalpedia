-- Prove2me | Theorems.Thm_EthierKurtz_martingale_solution_has_semigroup_conditional_expectation
-- name    : EthierKurtz.martingale_solution_has_semigroup_conditional_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T12:51:43.895704+00:00
-- url     : https://prove2.me/theorems/a99bfd3f-66b6-455c-a86b-151f694a2e5b
-- title:
--   Martingale solutions have the semigroup conditional expectation
-- statement:
--   For a solution of the martingale problem, conditional expectations of observables in L given the full process past equal evaluation of the characterization semigroup at the present state.

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

theorem EthierKurtz.martingale_solution_has_semigroup_conditional_expectation

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

    (T : ℝ → L →L[ℝ] L)
    (hT : (T 0 = ContinuousLinearMap.id ℝ L ∧
       (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
       (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
       (∀ f : L, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f))))
    (hTgen : (∀ f g : L,
        Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
          (f.val, g.val) ∈ closure (A' : Set _))) :
    ∀ (s t : ℝ≥0) (f : L),
      P[fun ω => (f.val : E → ℝ) (X (s + t) ω) | processPast X s] =ᵐ[P]
        fun ω => ((T (t : ℝ) f).val : E → ℝ) (X s ω) := by sorry
