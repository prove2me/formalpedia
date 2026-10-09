-- Prove2me | Theorems.Thm_FastCLO_ERM_lemma_1
-- name    : FastCLO.ERM.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:22:48.888931+00:00
-- url     : https://prove2.me/theorems/391578b0-e573-463a-b8a5-d43576c33a15
-- title:
--   Lemma 1 — under the noise condition, d(π*, π) ≤ 2d_Δ(π*, π) and d_Δ(π*, π) ≤ c₁ d(π*, π)^{α/(α+1)}
-- statement:
--   Let $\mathcal Z$ be a polytope with norm bound $B$ and extreme points $\mathcal Z^\angle$, and fix an instance with feature law $\mathbb P_X$ and regression function $f^*$. Suppose the noise condition (Assumption 2) holds with $\alpha, \gamma \ge 0$, and that $\mathbb P(|\mathcal Z^*(X)| > 1) = 0$. Let $\pi^* : \mathbb R^p \to \mathcal Z^\angle$ be an optimal policy, $\pi^*(x) \in \mathcal Z^*(x)$ for almost every $x$, and let $\pi : \mathbb R^p \to \mathcal Z^\angle$ be any policy, both measurable. Then
--
--   $$d(\pi^*, \pi) \le 2\, d_\Delta(\pi^*, \pi), \qquad d_\Delta(\pi^*, \pi) \le c_1\, d(\pi^*, \pi)^{\frac{\alpha}{\alpha+1}},$$
--
--   where $c_1 = (\alpha\gamma^\alpha)^{-\frac{\alpha}{\alpha+1}}(\alpha + 1)\gamma^\alpha$.
--
--   The lemma converts the excess cost of a policy into its disagreement probability with the optimal policy and back. It controls the variance of the excess-loss class in terms of its mean, which is the source of the fast rate.
--
--   **Formalization Note** Powers are real powers. At $\alpha = 0$ the constant is $c_1 = 1$ and the second claim reads $d_\Delta \le 1$. At $\gamma = 0 < \alpha$ the constant is $0$ (Lean's convention $0^{s} = 0$ for $s < 0$); the noise condition then forces $\Delta(X) = 0$, hence $\pi = \pi^*$, almost surely. Measurability of $\pi$ and $\pi^*$ is assumed so that $d$ and $d_\Delta$ are genuine expectations.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Lemma 1, A.4.2, p. 22

import Mathlib
import Definitions.Def_FastCLO_ERM_ERM
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ERM

/-- **Lemma 1** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear Optimization*,
arXiv:2011.03030v3, A.4.2, p. 22). Suppose Assumption 2 holds and `P(|Z*(X)| > 1) = 0`. Then for
the optimal policy `π*` and every policy `π : ℝ^p → Z∠`,
`d(π*, π) ≤ 2 d_Δ(π*, π)` and `d_Δ(π*, π) ≤ c₁ d(π*, π)^{α/(α+1)}`, where
`c₁ = (αγ^α)^{−α/(α+1)} (α + 1) γ^α`.

Formalization Note: `π*` is any policy with values in `Z∠` that is optimal at almost every `x`
(`πs x ∈ Z*(x)` a.e.); `P(|Z*(X)| > 1) = 0` is "`Z*(X)` is a subsingleton almost surely".
Measurability of `π` and `π*` is assumed so that `d` and `d_Δ` are genuine integrals and
probabilities. Powers are `Real.rpow`; at `α = 0` the constant is `c₁ = 1`, and at `γ = 0 < α` it
is `0` (Lean's `0 ^ (negative) = 0`), in which case Assumption 2 forces `π = π*` a.e. -/
theorem lemma_1 {p d : ℕ} (P : Polytope d) (I : Instance p d) (α γ : ℝ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hnoise : NoiseCond P I α γ)
    (huniq : ∀ᵐ x ∂I.μ, (Zstar P I x).Subsingleton)
    (πs π : Vec p → Vec d)
    (hπs : IsPolicy P πs) (hπs_meas : Measurable πs) (hπs_opt : ∀ᵐ x ∂I.μ, πs x ∈ Zstar P I x)
    (hπ : IsPolicy P π) (hπ_meas : Measurable π) :
    dExcess P I πs π ≤ 2 * dDelta I πs π ∧
      dDelta I πs π ≤
        (α * γ ^ α) ^ (-(α / (α + 1))) * (α + 1) * γ ^ α * dExcess P I πs π ^ (α / (α + 1)) := by sorry

end FastCLO.ERM
