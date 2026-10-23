-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_lemma_1
-- name    : AlmostSSDPortfolio.AASSD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:48.788884+00:00
-- url     : https://prove2.me/theorems/b078f5a7-03bf-4ac9-92e9-2cd5383bee6c
-- title:
--   Lemma 1, p. 45 — Var(X) + (b − E X)² = 2∫_a^b F^(2)(x) dx for a finite distribution on [a, b]
-- statement:
--   Let $X$ take the value $v_t$ with probability $p_t$, $t=1,\dots,m$, where $(p_t)$ is a probability vector and every $v_t$ lies in $[a,b]$, $a\le b$. Let $F^{(2)}(x)=\sum_tp_t(x-v_t)^+$ be its first-order lower partial moment, $\mathbb E X=\sum_tp_tv_t$ and $\mathrm{Var}(X)=\sum_tp_t(v_t-\mathbb EX)^2$. Then
--   $$\mathrm{Var}(X)+(b-\mathbb E X)^2=2\int_a^bF^{(2)}(x)\,dx.$$
--
--   Applied to the portfolio return and to the benchmark, this identity turns the numerator of the AASSD ratio into an integral of LPMs; it is the step (12b)→(12c) of the proof of Theorem 1.
--
--   **Formalization Note.** The paper states the lemma for a random variable bounded between $a$ and $b$; the mission uses it only for finitely supported laws, which is how it is stated here. $F^{(2)}$ is the LPM $\sum_tp_t(x-v_t)^+$, which equals $\int_{-\infty}^xF$ for the distribution function $F$. The hypothesis $a\le b$ (rather than $a<b$) is the natural generality.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 45, Appendix A, Lemma 1

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem lemma_1 {m : ℕ} (p v : Fin m → ℝ) (a b : ℝ) (hab : a ≤ b) (hp : IsProbVec p)
    (hv : ∀ t, v t ∈ Icc a b) :
    var p v + (b - mean p v) ^ 2 = 2 * ∫ x in a..b, lpm p v x := by sorry

end AlmostSSDPortfolio.AASSD
