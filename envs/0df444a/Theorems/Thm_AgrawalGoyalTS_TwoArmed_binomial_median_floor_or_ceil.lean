-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_binomial_median_floor_or_ceil
-- name    : AgrawalGoyalTS.TwoArmed.binomial_median_floor_or_ceil
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:07:29.851726+00:00
-- url     : https://prove2.me/theorems/dd3a6cc4-3e6b-41fb-999a-5372e073f3b4
-- title:
--   Fact 2 — the median of Binomial(n, p) is ⌊np⌋ or ⌈np⌉
-- statement:
--   An integer $m$ is a **median** of an integer-valued random variable $X$ if $\Pr(X\le m)\ge 1/2$ and $\Pr(X\ge m)\ge 1/2$. Let $n\in\mathbb N$ and $p\in[0,1]$, and let $X\sim\mathrm{Binomial}(n,p)$. Then $X$ has a median, and every median $m$ satisfies
--   $$m\in\{\lfloor np\rfloor,\ \lceil np\rceil\}.$$
--
--   The paper cites this from Jogdeo and Samuels (1968), reference [7]; the statement that every median lies between $\lfloor np\rfloor$ and $\lceil np\rceil$ is also in Kaas and Buhrman (1980). It is used in Lemma 3 in the form $F^B_{n,p}(\lceil np\rceil)\ge 1/2$.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 13, Fact 2 (citing [7] = Jogdeo and Samuels, Ann. Math. Statist. 39 (1968))

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

namespace AgrawalGoyalTS.TwoArmed

/-- Fact 2 (p. 13, from Kaas–Buhrman): `Binomial(n, p)` has a median, and every median is
`⌊np⌋` or `⌈np⌉`. -/
theorem binomial_median_floor_or_ceil (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ m : ℤ, IsBinomialMedian n p m) ∧
    ∀ m : ℤ, IsBinomialMedian n p m → m = ⌊(n : ℝ) * p⌋ ∨ m = ⌈(n : ℝ) * p⌉ := by sorry

end AgrawalGoyalTS.TwoArmed
