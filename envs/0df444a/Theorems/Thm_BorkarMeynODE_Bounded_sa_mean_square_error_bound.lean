-- Prove2me | Theorems.Thm_BorkarMeynODE_Bounded_sa_mean_square_error_bound
-- name    : BorkarMeynODE.Bounded.sa_mean_square_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:49:42.121307+00:00
-- url     : https://prove2.me/theorems/5b7b6c5d-4990-40a0-96ff-5251b86064a7
-- title:
--   Theorem 2.3(ii) — mean-square error of order $\bar\alpha$ under exponential stability
-- statement:
--   Assume (A1) for $h$ and $h_\infty$, and let $C_0$ be the constant of (A2). Suppose $x^* \in \mathbb{R}^d$ is a globally asymptotically stable equilibrium of the ODE (1.2) $\dot x = h(x)$, and that it is moreover globally exponentially asymptotically stable. Then there exist $\alpha^* > 0$ and $b_2 < \infty$ such that the following holds. Whenever the stepsizes satisfy (BS) with bounds $\underline\alpha < \bar\alpha \le \alpha^*$, $X$ follows the recursion (1.1) with noise $M$ satisfying (A2) with constant $C_0$, and $X(0) = x_0 \in \mathbb{R}^d$ is deterministic, the error $e(n) = \|X(n) - x^*\|$ of (2.2) satisfies
--
--   $$\limsup_{n \to \infty} \mathsf E\big[e(n)^2\big] \le b_2\, \bar\alpha.$$
--
--   The constant $b_2$ depends only on $h$, $h_\infty$, $C_0$ and $x^*$. It is uniform over the stepsizes and over the initial condition, so the asymptotic mean-square error of stochastic approximation with non-vanishing stepsize is proportional to the largest stepsize.
--
--   **Formalization Note** The page says "for any $0 < \alpha \le \alpha^*$ … there exists $b_2 < \infty$"; the unbarred $\alpha$ is a typo for $\bar\alpha$, and read literally that order would allow $b_2 = C_1/\bar\alpha$, which makes the claim empty. The proof gives $\limsup_j \mathsf E[e(m(j))^2] \le 16 C_3 \bar\alpha$, a constant times $\bar\alpha$, which is the uniform statement given here. $\alpha^*$ is existentially quantified rather than tied to the witness of Theorem 2.1(ii). Moments and the $\limsup$ are computed in $[0,\infty]$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 451, Theorem 2.3(ii)

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability
import Definitions.Def_BorkarMeynODE_Bounded_SAModel

namespace BorkarMeynODE.Bounded

open MeasureTheory Filter Topology

/-- Theorem 2.3(ii) (Borkar–Meyn 2000, p. 451). Assume (A1), (A2) and (BS), and let `x⋆` be a
globally asymptotically stable equilibrium of (1.2) `ẋ = h(x)` which is moreover globally
exponentially asymptotically stable. Then there are `α* > 0` and `b₂ < ∞` such that for every
`0 < ᾱ ≤ α*` and every deterministic initial condition `X(0) ∈ ℝ^d`,
`limsup_n E[e(n)²] ≤ b₂ ᾱ`, where `e(n) = ‖X(n) − x⋆‖` (2.2).
`b₂` is uniform in the stepsizes and in `X(0)` (the page's order would make it trivial);
the page's `0 < α ≤ α*` means `0 < ᾱ ≤ α*`. -/
theorem sa_mean_square_error_bound {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) (C₀ : ℝ) (xstar : EuclideanSpace ℝ (Fin d))
    (hgas : IsGloballyAsymptoticallyStable h xstar)
    (hges : IsGloballyExponentiallyStable h xstar) :
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ b₂ : ℝ,
      ∀ (αlo αhi : ℝ) (a : ℕ → ℝ), BoundedStepsize αlo αhi a → αhi ≤ αstar →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n)),
        (∀ n, StronglyMeasurable (M n)) → IsSARecursion h a X M →
        AssumptionA2 P X M hX C₀ →
        ∀ x₀ : EuclideanSpace ℝ (Fin d), (∀ ω, X 0 ω = x₀) →
        limsup (fun n : ℕ => ∫⁻ ω, ‖X n ω - xstar‖ₑ ^ 2 ∂P) atTop
          ≤ ENNReal.ofReal (b₂ * αhi) := by sorry

end BorkarMeynODE.Bounded
