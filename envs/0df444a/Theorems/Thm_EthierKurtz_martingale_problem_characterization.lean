-- Prove2me | Theorems.Thm_EthierKurtz_martingale_problem_characterization
-- name    : EthierKurtz.martingale_problem_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T18:49:07.667056+00:00
-- url     : https://prove2.me/theorems/b1aead5f-a162-44e9-8769-22dcd424b5a9
-- title:
--   Theorem 4.1 — Martingale characterization of Markov processes
-- statement:
--   Let E be a separable metric space and A a dissipative linear relation of bounded real Borel functions. Suppose A′ is a linear subrelation and the uniform closures of its domain and of the range of λ−A′ equal L for some λ>0, where L determines Borel probability measures by integration. Given a solution X of (A,μ), there is a strongly continuous contraction semigroup on L whose generator graph is the closure of A′; X corresponds to this semigroup, is Markov with respect to its natural past, and has the same finite-dimensional distributions as every other solution with initial law μ on any probability space.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986; Chapter 4, Section 4, Theorem 4.1, printed p.182 (PDF p.191); equation (3.4), printed p.174 (PDF p.183); equation (4.2), printed p.183 (PDF p.192).

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace EthierKurtz

variable {E Ω Ω' : Type*} [MeasurableSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem martingale_problem_characterization
    [MetricSpace E] [BorelSpace E] [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) →
      ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E) (hX : SolvesMartingaleProblem A μ P X) :
    (∃ T : ℝ → L →L[ℝ] L,
      (T 0 = ContinuousLinearMap.id ℝ L ∧
       (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
       (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
       (∀ f : L, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f))) ∧
      (∀ f g : L,
        Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
          (f.val, g.val) ∈ closure (A' : Set _)) ∧
      (∀ (s t : ℝ≥0) (f : L),
        P[fun ω => (f.val : E → ℝ) (X (s + t) ω) | processPast X s] =ᵐ[P]
          fun ω => ((T (t : ℝ) f).val : E → ℝ) (X s ω))) ∧
    (∀ (s t : ℝ≥0) (f : UniformBoundedFunction E), Measurable (f : E → ℝ) →
      P[fun ω => f (X (s + t) ω) | processPast X s] =ᵐ[P]
        P[fun ω => f (X (s + t) ω) |
          MeasurableSpace.comap (X s) ‹MeasurableSpace E›]) ∧
    (∀ (Q : Measure Ω'), IsProbabilityMeasure Q → ∀ Y : ℝ≥0 → Ω' → E,
      SolvesMartingaleProblem A μ Q Y → ∀ (n : ℕ) (t : Fin n → ℝ≥0),
        Measure.map (fun ω i => X (t i) ω) P =
          Measure.map (fun ω i => Y (t i) ω) Q) := by sorry

end EthierKurtz
