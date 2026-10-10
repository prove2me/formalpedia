-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_fluid_bayes_selector_regret
-- name    : BayesProphet.MultiSec.fluid_bayes_selector_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:30.95724+00:00
-- url     : https://prove2.me/theorems/9ea85720-f71c-4714-a919-3f849ad27d40
-- title:
--   Theorem 2 — constant regret of the Fluid Bayes Selector for multi-secretary
-- statement:
--   Consider the multi-secretary problem with $n\ge1$ types, multinomial arrivals with probabilities $p_j>0$, $\sum_jp_j=1$, and rewards sorted as $r_1\ge r_2\ge\dots\ge r_n\ge0$. Let $r_{\max}=\max_jr_j$ and $p_{\min}=\min_jp_j$. For every horizon $T\in\mathbb N$ and every initial budget $B\in\mathbb N$, the expected regret of the Fluid Bayes Selector (Algorithm 2, in its rounded form of Appendix B.3) satisfies
--   $$\mathbb E[\mathrm{Reg}]\ \le\ r_{\max}\sum_{j>1}\frac{2}{p_j}\ \le\ \frac{2(n-1)\,r_{\max}}{p_{\min}}.$$
--
--   The regret is measured against Offline, the full-information optimum of the Bellman equation (2), and the bound does not depend on $T$ or $B$.
--
--   **Formalization Note** The expectation is the explicit finite sum over the $n^T$ type sequences weighted by $\prod_tp_{\theta^t}$. Lean index `0` is the paper's type $1$; the order $r_1\ge\dots\ge r_n$ (the paper's w.l.o.g.) is `Antitone r`, ties allowed. Non-negative rewards are the paper's implicit assumption (rewards are abilities) made explicit. The policy is the one of Appendix B.3, which always accepts type $1$ when the budget is positive; Algorithm 2 read literally differs on type $1$ (see the mission description).
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 18, Theorem 2 (proof: pp. 36–37, Appendix B.3)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec

theorem fluid_bayes_selector_regret {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j) (T B : ℕ) :
    expectedRegret p r T B ≤
        Finset.univ.sup' Finset.univ_nonempty r * ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ∧
    Finset.univ.sup' Finset.univ_nonempty r * ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ≤
        2 * ((n : ℝ) - 1) * Finset.univ.sup' Finset.univ_nonempty r /
          Finset.univ.inf' Finset.univ_nonempty p := by sorry

end BayesProphet.MultiSec
