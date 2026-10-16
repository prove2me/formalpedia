-- Prove2me | Theorems.Thm_BreakingSample_Conservative_lemma_7
-- name    : BreakingSample.Conservative.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:34.047998+00:00
-- url     : https://prove2.me/theorems/078479e6-ed58-4055-8a57-84485f62275f
-- title:
--   Lemma 7, p. 19 — the conservative policy loses at most ξ/(1−γ) in its own MDP: V̂^π − V̂^{π̂c} ≤ ξ/(1−γ)
-- statement:
--   Let $\widehat{\mathcal M} = (\mathcal S, \mathcal A, \widehat P, r, \gamma)$ be a finite discounted MDP (kernel $\widehat P$, rewards in $[0,1]$, $\gamma\in(0,1)$) with a linearly ordered action set, and let $\widehat Q^\star$, $\widehat V^\star$ be its optimal Q- and value functions. Let $\varsigma \le \xi$ and let $\widehat\pi_{\mathrm c}$ follow the conservative rule $\widehat\pi_{\mathrm c}(s) = \min\{a : \widehat Q^\star(s,a) > \widehat V^\star(s) - \varsigma\}$. Then for every deterministic policy $\pi$ and every state $s$,
--
--   $$\widehat V^{\pi}(s) - \widehat V^{\widehat\pi_{\mathrm c}}(s) \le \frac{\xi}{1-\gamma}.$$
--
--   In the paper $\pi = \pi^\star$, the optimal policy of the true MDP, and $\widehat P$ is the empirical kernel; the bound controls the middle term of the decomposition (51) of $V^\star - V^{\widehat\pi_{\mathrm c}}$.
--
--   **Formalization Note** The statement holds for any kernel and for any policy $\pi$ in place of $\pi^\star$, which is stronger than the page (the paper's proof ends with $\widehat V^{\pi^\star} \le \widehat V^\star$, valid for every $\pi$). Only $\varsigma \le \xi$ is assumed; the rule cannot hold for $\varsigma \le 0$, so $\varsigma \in [0,\xi]$ of the page is implied.
-- source:
--   arXiv:2005.12900v8, Lemma 7, p. 19, (52); proof in App. B.6, p. 33

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Conservative_Rule

namespace BreakingSample.Conservative

theorem lemma_7 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [LinearOrder A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (ξ ς : ℝ) (hς : ς ≤ ξ) (πc : S → A)
    (hc : IsConservative (BreakingSample.Perturbed.optQ P r γ) (BreakingSample.Perturbed.optValue P r γ) ς πc) (π : S → A) :
    ∀ s, BreakingSample.Perturbed.value P r γ π s - BreakingSample.Perturbed.value P r γ πc s ≤ ξ / (1 - γ) := by sorry

end BreakingSample.Conservative
