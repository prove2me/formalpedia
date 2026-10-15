-- Prove2me | Theorems.Thm_CommitteeVoting_SingleVoter_lemma_5
-- name    : CommitteeVoting.SingleVoter.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:36.479368+00:00
-- url     : https://prove2.me/theorems/55527326-4bc9-4fdb-ae94-6c8c90b8b7ea
-- title:
--   Lemma 5, p. 49 — raising every Poisson binomial parameter gives a stochastically larger law
-- statement:
--   Let $X$ be Poisson binomial with parameters $p_1, \dots, p_n$ and $X'$ Poisson binomial with parameters $p'_1, \dots, p'_n$, where all parameters lie in $[0,1]$ and $p_i \le p'_i$ for $i = 1, \dots, n$. Then $X \le_{\mathrm{st}} X'$, that is (Definition 9, (97)),
--
--   $$
--   F_{X'}(x) \le F_X(x) \qquad \text{for all } x,
--   $$
--
--   where $F_X(x) = \Pr[X \le x]$.
--
--   Increasing the success probability of each independent trial can only shift the number of successes upward in the usual stochastic order; Lemma 1 follows from this together with Lemma 4.
--
--   **Formalization Note** The hypotheses $0 \le p_i$ and $p'_i \le 1$ make the parameters probabilities, which the printed lemma leaves implicit in "Poisson Binomial random variable with parameters". The inequality is stated for natural thresholds $x$; since both laws live on $\{0, \dots, n\}$, this is equivalent to all real $x$ ($F(x) = F(\lfloor x \rfloor)$ for $x \ge 0$, $F(x) = 0$ for $x < 0$). Indices are 0-based.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 49, Lemma 5; p. 51, Definition 9 (97)

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace CommitteeVoting.SingleVoter

/-- Lemma 5 (p. 49): raising every parameter of a Poisson binomial law makes it stochastically
larger, `X ≤_st X'`, i.e. (Definition 9, (97)) `F_{X'}(x) ≤ F_X(x)` for every threshold `x`. -/
theorem lemma_5 {n : ℕ} (p p' : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hpp' : ∀ i, p i ≤ p' i)
    (hp'1 : ∀ i, p' i ≤ 1) (x : ℕ) :
    pbCDF p' Finset.univ x ≤ pbCDF p Finset.univ x := by sorry

end CommitteeVoting.SingleVoter
