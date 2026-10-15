-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_theorem_1
-- name    : BreakingSample.Perturbed.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:32.803887+00:00
-- url     : https://prove2.me/theorems/644595e5-344a-4c63-98e8-fcc8728b3652
-- title:
--   Theorem 1 — perturbed model-based planning achieves ε value and γε action-value error
-- statement:
--   Consider a finite discounted MDP with rewards in $[0,1]$. Draw $N$ independent next-state samples for each state-action pair and form $\widehat P$. Independently perturb each reward by $\zeta(s,a)\sim\operatorname{Unif}(0,\xi)$, and let $\widehat\pi_p^\star$ be any optimal policy for $(\widehat P,r+\zeta,\gamma)$. There are absolute constants $c_0,c_1>0$ such that for every $\delta>0$ and $0<\varepsilon\le 1/(1-\gamma)$, if $\xi=c_1(1-\gamma)\varepsilon/(|S|^5|A|^5)$ and
--
--   $$N\ge\frac{c_0\log(|S||A|/((1-\gamma)\varepsilon\delta))}{(1-\gamma)^3\varepsilon^2},$$
--
--   then with probability at least $1-\delta$, simultaneously for all $(s,a)$,
--
--   $$V^{\widehat\pi_p^\star}(s)\ge V^\star(s)-\varepsilon,\qquad Q^{\widehat\pi_p^\star}(s,a)\ge Q^\star(s,a)-\gamma\varepsilon.$$
--
--   The guarantee controls the policy obtained from the perturbed empirical model when it is evaluated in the original, unperturbed MDP.
--
--   **Formalization Note** The constants precede the MDP and sample parameters. The result covers every optimal empirical policy; $N>0$ and a nonempty state set express the source's sampling and cardinality conventions. The QVI/PI iteration-count sentence following (12) is outside this goal.
-- source:
--   arXiv:2005.12900v8, Theorem 1, (9), (11)–(12), p. 8

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.Perturbed

/-- Theorem 1, (11)–(12), arXiv:2005.12900v8, p. 8. -/
theorem theorem_1 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (S A : Type) [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A] [Nonempty A]
      (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ), IsDiscountedMDP P r γ →
    ∀ (δ ε : ℝ) (N : ℕ), 0 < δ → 0 < ε → ε ≤ 1 / (1 - γ) → 0 < N →
      c₀ * Real.log ((Fintype.card S : ℝ) * Fintype.card A / ((1 - γ) * ε * δ))
          / ((1 - γ) ^ 3 * ε ^ 2) ≤ (N : ℝ) →
      jointProb P N
        (unifCube S A (c₁ * (1 - γ) * ε / ((Fintype.card S : ℝ) ^ 5 * (Fintype.card A : ℝ) ^ 5)))
        (fun x ζ => ¬ ∀ π : S → A, IsOptimal (empKernel x) (fun s a => r s a + ζ s a) γ π →
          ∀ s a, optValue P r γ s - ε ≤ value P r γ π s ∧
                 optQ P r γ s a - γ * ε ≤ qValue P r γ π s a) ≤ δ := by sorry

end BreakingSample.Perturbed
