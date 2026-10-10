-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_binomial_chernoff_hoeffding
-- name    : BayesProphet.MultiSec.binomial_chernoff_hoeffding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:07.555657+00:00
-- url     : https://prove2.me/theorems/7af15251-dd6a-4fbb-930b-81937dd13c16
-- title:
--   Eq. (18) — Chernoff–Hoeffding bound for the binomial distribution
-- statement:
--   Let $t\in\mathbb N$, $\alpha\in[0,1]$, $\varepsilon\ge 0$, and $X\sim\mathrm{Bin}(t,\alpha)$, so that $\mathbb E[X]=t\alpha$. Then
--   $$\mathbb P\big[X-\mathbb E[X]\le -t\varepsilon\big]\le e^{-2\varepsilon^2 t},\qquad \mathbb P\big[X-\mathbb E[X]\ge t\varepsilon\big]\le e^{-2\varepsilon^2 t}.$$
--
--   The paper quotes this from Dubhashi–Panconesi [22, Theorem 1.1] and uses it with $\varepsilon=p_j/2$ to bound the disagreement probabilities of the Fluid Bayes Selector.
--
--   **Formalization Note** The probabilities are written as sums of the binomial mass function $\binom tk\alpha^k(1-\alpha)^{t-k}$ over $k\in\{0,\dots,t\}$. The hypothesis $\varepsilon\ge0$ is implicit in the paper (the bound is false for $\varepsilon<0$).
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 37, Eq. (18)

import Mathlib

namespace BayesProphet.MultiSec

theorem binomial_chernoff_hoeffding (t : ℕ) (α ε : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hε : 0 ≤ ε) :
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * α ≤ -(t * ε)),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) ∧
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * α),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) := by sorry

end BayesProphet.MultiSec
