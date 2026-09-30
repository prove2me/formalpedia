-- Prove2me | Theorems.Thm_BorkarMeynODE_Bounded_sa_second_moment_limsup_bounded
-- name    : BorkarMeynODE.Bounded.sa_second_moment_limsup_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:48:32.087594+00:00
-- url     : https://prove2.me/theorems/854efba7-5ec1-4e8b-9256-77327c5a05af
-- title:
--   Theorem 2.1(ii) — under (BS) with small $\bar\alpha$, $\limsup_n \mathsf E\|X(n)\|^2$ is bounded
-- statement:
--   Assume (A1) for $h$ and $h_\infty$, and let $C_0$ be the constant of (A2). Then there exist $\alpha^* > 0$ and $C_1 < \infty$ such that the following holds. Whenever the stepsizes satisfy (BS) with bounds $\underline\alpha < \bar\alpha$ and $\bar\alpha < \alpha^*$, $X$ follows the recursion (1.1) with noise $M$ satisfying (A2) with constant $C_0$, and $X(0) = x_0 \in \mathbb{R}^d$ is deterministic,
--
--   $$\limsup_{n \to \infty} \mathsf E\big[\|X(n)\|^2\big] \le C_1.$$
--
--   The constants $\alpha^*$ and $C_1$ depend only on $h$, $h_\infty$ and $C_0$, not on the stepsizes, the process or the initial condition. This is the stability half of the paper's main result for bounded, non-vanishing stepsizes: stability of the fluid ODE at infinity implies stability of the algorithm in mean square.
--
--   **Formalization Note** Second moments and the $\limsup$ are computed in $[0,\infty]$, so an unbounded sequence of moments has $\limsup = \infty$ and the bound is a genuine finiteness claim. The paper's "for all $X(0) \in \mathbb R^d$" is read as a deterministic initial condition.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 450, Theorem 2.1(ii)

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability
import Definitions.Def_BorkarMeynODE_Bounded_SAModel

namespace BorkarMeynODE.Bounded

open MeasureTheory Filter Topology

/-- Theorem 2.1(ii) (Borkar–Meyn 2000, p. 450). Under (A1), (A2) and (BS) there exist `α* > 0`
and `C₁ < ∞` such that for every `0 < ᾱ < α*` and every deterministic initial condition
`X(0) ∈ ℝ^d`, `limsup_n E‖X(n)‖² ≤ C₁`. The constants `α*`, `C₁` depend only on `h`, `h_∞`
and `C₀`: they come before the stepsizes, the process and `X(0)`. Second moments and the
`limsup` are taken in `ℝ≥0∞`. -/
theorem sa_second_moment_limsup_bounded {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) (C₀ : ℝ) :
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ C₁ : ℝ,
      ∀ (αlo αhi : ℝ) (a : ℕ → ℝ), BoundedStepsize αlo αhi a → αhi < αstar →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n)),
        (∀ n, StronglyMeasurable (M n)) → IsSARecursion h a X M →
        AssumptionA2 P X M hX C₀ →
        ∀ x₀ : EuclideanSpace ℝ (Fin d), (∀ ω, X 0 ω = x₀) →
        limsup (fun n : ℕ => ∫⁻ ω, ‖X n ω‖ₑ ^ 2 ∂P) atTop ≤ ENNReal.ofReal C₁ := by sorry

end BorkarMeynODE.Bounded
