-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_theorem_1
-- name    : EndogBudgetAds.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:48.946173+00:00
-- url     : https://prove2.me/theorems/cc2d7092-17c8-435e-90ab-c58e3c643d77
-- title:
--   Theorem 1, p. 20 — σ* is an ε-approximate equilibrium with ε = 11ϑ² log(m)/m^{1/ϑ}
-- statement:
--   Consider the sponsored-search market with $m$ bidders, $n$ items, exponential valuations $V_{ij} \sim \mathrm{Exp}(\lambda_j)$, budget cost rates $r_j \ge 0$, $\theta_j = \lambda_j(1+r_j) \in [\theta_{\min}, \theta_{\max}]$, $\vartheta = \theta_{\max}/\theta_{\min}$, and outside value $0 < \delta \le \log(4/3)/\theta_{\max}$, in which the ad network allocates by an optimal solution of its LP (2). Let σ* be the profile in which bidder $j$ bids $W_j = V_j/(1+r_j)$ with budget $B^*_j = \mathbb E_{-j}[\bar\Psi_j](1 + 2\vartheta/m^{1/\vartheta})$.
--
--   There is a constant $C > 0$, independent of the market, such that if
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta + 5\vartheta\log\vartheta + 1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)}\log(m)/C,$$
--   then for every bidder $j$ and every deviation $\sigma_j$,
--   $$\mathbb E\big[\pi_j(\sigma_j, \sigma^*_{-j})\big] \le \mathbb E\big[\pi_j(\sigma^*)\big]\Big(1 + \frac{11\vartheta^2\log m}{m^{1/\vartheta}}\Big).$$
--   Consequently σ* is an $\epsilon$-approximate equilibrium with $\epsilon = 11\vartheta^2\log(m)/m^{1/\vartheta}$.
--
--   This is the paper's main result: in large markets, shading valuations by $1+r_j$ and declaring a budget with a small multiplicative slack over the expected unbudgeted spend is an approximate equilibrium, and the error vanishes as $m \to \infty$.
--
--   **Formalization Note** The theorem holds for every measurable selection of optimal solutions of (2), fixed before the strategies and used on both sides. Deviations are deterministic admissible strategies (measurable, finite nonnegative budget); a randomized deviation is a mixture of these. $C$ is quantified before the market, so it is universal ("a fixed constant independent of $m$"; Lemma 7's proof gives $C = 6c/7$ with an absolute constant $c$). $\theta_{\min}, \theta_{\max}$ are the parameters of p. 18, not the extreme $\theta_j$. Expectations are Bochner integrals: the positive part of $\pi_j$ is integrable; if a deviation's budget is not integrable the true expected payoff is $-\infty$ and the Lean left-hand side is $0$, which is still at most the right-hand side because $\mathbb E[\pi_j(\sigma^*)] > 0$. $\log$ is natural; real powers are `Real.rpow`.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 20, Theorem 1 (Definitions 2–3, p. 17; σ* (3)–(4), p. 18)

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Theorem 1, p. 20: there is a constant `C > 0` independent of the market such that, for
`m ≥ max{(2ϑ)^ϑ, exp(3ϑ + 5ϑ log ϑ + 1)}` and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, no admissible deviation
`σ_j` of any bidder `j` from σ* raises her expected payoff above `E[π_j(σ*)] (1 + 11ϑ² log(m)/m^{1/ϑ})`;
consequently σ* is an `ε`-approximate equilibrium with `ε = 11ϑ² log(m)/m^{1/ϑ}`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 5 * vt M * Real.log (vt M) + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
        (∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
          ∫ V, payoff M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M ≤
            (∫ V, payoff M alloc (sigmaStar M) j V ∂ valLaw M) *
              (1 + 11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M))) ∧
        IsEpsEquilibrium M alloc (sigmaStar M)
          (11 * vt M ^ 2 * Real.log M.m / (M.m : ℝ) ^ (1 / vt M)) := by sorry

end EndogBudgetAds.Equilibrium
