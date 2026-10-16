-- Prove2me | Theorems.Thm_BreakingSample_Conservative_theorem_2
-- name    : BreakingSample.Conservative.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:27.756204+00:00
-- url     : https://prove2.me/theorems/0e3d3058-ccb2-4e0a-a9f9-96b3eac6ddf3
-- title:
--   Theorem 2, p. 8 — the conservative model-based policy π̂c of (10) is ε-optimal w.p. ≥ 1 − δ under the sample size and ξ of Theorem 1
-- statement:
--   There exist universal constants $c_0, c_1 > 0$ such that the following holds. Let $\mathcal M = (\mathcal S,\mathcal A,P,r,\gamma)$ be any finite discounted MDP with rewards in $[0,1]$, $\gamma\in(0,1)$ and actions $\mathcal A = \{1,\dots,|\mathcal A|\}$. Let $\delta > 0$ and $0 < \varepsilon \le \frac{1}{1-\gamma}$, set $\xi = \frac{c_1(1-\gamma)\varepsilon}{|\mathcal S|^5|\mathcal A|^5}$, and suppose the number of samples per state–action pair satisfies
--
--   $$N \ge \frac{c_0\log\big(\frac{|\mathcal S||\mathcal A|}{(1-\gamma)\varepsilon\delta}\big)}{(1-\gamma)^3\varepsilon^2}.$$
--
--   Let $\widehat Q^\star$, $\widehat V^\star$ be the optimal Q- and value functions of the empirical MDP $(\mathcal S,\mathcal A,\widehat P,r,\gamma)$, draw $\varsigma\sim\mathrm{Unif}(0,\xi)$ independently of the data, and let $\widehat\pi_{\mathrm c}(s) = \min\{a : \widehat Q^\star(s,a) > \widehat V^\star(s) - \varsigma\}$ as in (10). Then with probability at least $1-\delta$,
--
--   $$\forall (s,a)\in\mathcal S\times\mathcal A, \qquad V^{\widehat\pi_{\mathrm c}}(s) \ge V^\star(s) - \varepsilon \quad\text{and}\quad Q^{\widehat\pi_{\mathrm c}}(s,a) \ge Q^\star(s,a) - \gamma\varepsilon,$$
--
--   where $V^{\widehat\pi_{\mathrm c}}$, $Q^{\widehat\pi_{\mathrm c}}$, $V^\star$, $Q^\star$ are computed in the true MDP.
--
--   The conservative planner reaches the minimax-optimal sample size of Theorem 1 without perturbing the rewards: it only breaks ties among near-optimal actions in a randomized but structured way.
--
--   **Formalization Note** "Under the same assumptions of Theorem 1" is formalized with its own universal constants $c_0, c_1$, placed before every type and parameter. The probability is over the data and $\varsigma$ jointly (outer measure in $\varsigma$), and the event is the failure of the conclusion for every policy satisfying (10). $0 < N$ is added as the standing assumption of (3), which divides by $N$. The order of $\mathcal A$ is any linear order on the finite action type.
-- source:
--   arXiv:2005.12900v8, Theorem 2, p. 8, (13); algorithm (10), p. 8; Theorem 1, p. 8, (12)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Conservative_Rule

namespace BreakingSample.Conservative

theorem theorem_2 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (S A : Type) [Fintype S] [DecidableEq S] [Fintype A] [LinearOrder A] [Nonempty A]
      (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ), BreakingSample.Perturbed.IsDiscountedMDP P r γ →
    ∀ (δ ε : ℝ) (N : ℕ), 0 < δ → 0 < ε → ε ≤ 1 / (1 - γ) → 0 < N →
      c₀ * Real.log ((Fintype.card S : ℝ) * Fintype.card A / ((1 - γ) * ε * δ))
          / ((1 - γ) ^ 3 * ε ^ 2) ≤ (N : ℝ) →
      BreakingSample.Perturbed.jointProb P N
        (BreakingSample.Perturbed.unifInterval (c₁ * (1 - γ) * ε / ((Fintype.card S : ℝ) ^ 5 * (Fintype.card A : ℝ) ^ 5)))
        (fun x ς => ¬ ∀ π : S → A,
          IsConservative (BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.empKernel x) r γ) (BreakingSample.Perturbed.optValue (BreakingSample.Perturbed.empKernel x) r γ) ς π →
          ∀ s a, BreakingSample.Perturbed.optValue P r γ s - ε ≤ BreakingSample.Perturbed.value P r γ π s ∧
                 BreakingSample.Perturbed.optQ P r γ s a - γ * ε ≤ BreakingSample.Perturbed.qValue P r γ π s a) ≤ δ := by sorry

end BreakingSample.Conservative
