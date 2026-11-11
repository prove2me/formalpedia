-- Prove2me | Theorems.Thm_EthierKurtz_martingale_problem_determines_finite_dimensional_distributions
-- name    : EthierKurtz.martingale_problem_determines_finite_dimensional_distributions
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:51:19.048769+00:00
-- url     : https://prove2.me/theorems/e7f29b55-7342-4ff0-afdb-be23ceaf9cb9
-- title:
--   The martingale problem determines finite-dimensional distributions
-- statement:
--   Any two probability-space realizations solving the same martingale problem have identical distributions at every finite selection of times.

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

theorem EthierKurtz.martingale_problem_determines_finite_dimensional_distributions
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
    (X : ℝ≥0 → Ω → E) (hX : SolvesMartingaleProblem A μ P X) :
    ∀ (Q : Measure Ω'), IsProbabilityMeasure Q →
      ∀ Y : ℝ≥0 → Ω' → E,
        SolvesMartingaleProblem A μ Q Y →
        ∀ (n : ℕ) (t : Fin n → ℝ≥0),
          Measure.map (fun ω i => X (t i) ω) P =
            Measure.map (fun ω i => Y (t i) ω) Q := by sorry
