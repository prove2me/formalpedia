-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_binom_cdf_hoeffding
-- name    : AgrawalGoyalTS.TwoArmed.binom_cdf_hoeffding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:08:13.45715+00:00
-- url     : https://prove2.me/theorems/c69ab45e-f26b-4742-b1a2-286e08fc1d1a
-- title:
--   Lemma 6 — Hoeffding bounds on binomial cdfs, (10) and (11)
-- statement:
--   Let $n$ be a natural number, $p\in[0,1]$ and $\delta\ge 0$, and let $F^B_{n,p}(x)=\Pr(\mathrm{Binomial}(n,p)\le x)$ for real $x$. Then
--   $$F^B_{n,p}(np-n\delta)\le e^{-2n\delta^2},\qquad 1-F^B_{n,p}(np+n\delta)\le e^{-2n\delta^2},\tag{10}$$
--   $$1-F^B_{n+1,p}(np+n\delta)\le\frac{e^{4\delta}}{e^{2n\delta^2}}.\tag{11}$$
--
--   These are the concentration estimates used in the proofs of Lemmas 2 and 3.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 13, Lemma 6, Eqs. (10)–(11)

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

namespace AgrawalGoyalTS.TwoArmed

/-- Lemma 6 (p. 13), (10) and (11): for every natural `n`, `p ∈ [0,1]` and `δ ≥ 0`,
`F^B_{n,p}(np - nδ) ≤ e^{-2nδ²}`, `1 - F^B_{n,p}(np + nδ) ≤ e^{-2nδ²}` and
`1 - F^B_{n+1,p}(np + nδ) ≤ e^{4δ} / e^{2nδ²}`. -/
theorem binom_cdf_hoeffding (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    binomCDF n p ((n : ℝ) * p - (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF n p ((n : ℝ) * p + (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF (n + 1) p ((n : ℝ) * p + (n : ℝ) * δ) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by sorry

end AgrawalGoyalTS.TwoArmed
