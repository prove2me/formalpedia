-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_inverse_bernoulli_bounds
-- name    : ConformalBeyondExchangeability.inverse_bernoulli_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:52:31.820249+00:00
-- url     : https://prove2.me/theorems/ab643fbd-9587-4d7c-bebb-1368f5ba2150
-- title:
--   Lemma 3: bounds on an inverse weighted sum of Bernoulli variables
-- statement:
--   Let $p_1,\dots,p_n,a_1,\dots,a_n\in[0,1]$ with $a_1+\dots+a_n>0$, and let $B_1,\dots,B_n$ be independent with $B_i\sim\mathrm{Bernoulli}(p_i)$. Then
--   $$\frac{a_1+\dots+a_n+1}{a_1p_1+\dots+a_np_n+1}\le\mathbb E\Big[\frac{a_1+\dots+a_n+1}{a_1B_1+\dots+a_nB_n+1}\Big]\le\frac{a_1+\dots+a_n}{a_1p_1+\dots+a_np_n}.$$
--
--   The upper bound converts the conditional bound in the proof of Theorem 6 into the factor $1/(1-\sum_i\bar w_i\,\mathsf d_{\mathrm{mix}}(Z_i,Z_{n+1}))$.
--
--   **Formalization Note** The expectation is the finite sum over $b\in\{0,1\}^n$. The upper bound is stated in $[0,\infty]$ with $x/0=+\infty$ for $x>0$, so the case $a_1p_1+\dots+a_np_n=0$, where the right side is $+\infty$, is included.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Appendix E.5, Lemma 3, p. 53; proof in Appendix E.5.1, pp. 54-56

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem inverse_bernoulli_bounds {n : ℕ} (p a : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hapos : 0 < ∑ i, a i) :
    (∑ i, a i + 1) / (∑ i, a i * p i + 1) ≤ bernoulliExp p (invBernoulliRatio a) ∧
      ENNReal.ofReal (bernoulliExp p (invBernoulliRatio a)) ≤
        ENNReal.ofReal (∑ i, a i) / ENNReal.ofReal (∑ i, a i * p i) := by sorry

end ConformalBeyondExchangeability
