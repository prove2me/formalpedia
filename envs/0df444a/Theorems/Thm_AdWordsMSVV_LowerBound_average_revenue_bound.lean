-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_average_revenue_bound
-- name    : AdWordsMSVV.LowerBound.average_revenue_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:44.494534+00:00
-- url     : https://prove2.me/theorems/686f4293-cffa-4118-9578-a89111bdc3f1
-- title:
--   Proof of Theorem 9, p. 15 — every deterministic algorithm earns on average at most (1 − 1/e + δ)·N·B over the distribution D, for N large
-- statement:
--   For every $\delta > 0$ there is $N_0$ such that for every $N \ge N_0$, every budget $B \ge 1$ and every deterministic online algorithm $a$ for instances with $N$ bidders and $NB$ queries, the average revenue of $a$ over the uniform distribution $\mathcal D$ on the permuted round instances satisfies
--   $$\frac{1}{N!}\sum_{\pi}\mathrm{ALG}_a(I_\pi) \le \Big(1-\frac1e+\delta\Big)NB.$$
--
--   In the paper's units (budget $1$, bids $\epsilon=1/B$) the right-hand side is $(1-1/e+\delta)N$: the expected revenue of any deterministic algorithm on $\mathcal D$ is asymptotically at most a $(1-1/e)$ fraction of the optimum $N$. Together with the Yao step and the value of the optimum, this gives Theorem 9.
--
--   **Formalization Note** The paper's "at most $N(1-1/e)$" is asymptotic (see the summed-bound milestone), hence the slack $\delta$. The threshold $N_0$ depends on $\delta$ only, not on the budget $B$ or the algorithm.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, last paragraph, second sentence

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

theorem average_revenue_bound :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : ℕ, 1 ≤ B →
      ∀ a : DetAlg N (N * B),
        permAvg N (fun π => (revenue B (roundInstance N B π) a : ℝ))
          ≤ (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by sorry

end AdWordsMSVV.LowerBound
