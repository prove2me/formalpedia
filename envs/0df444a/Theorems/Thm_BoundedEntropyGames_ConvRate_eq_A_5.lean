-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_A_5
-- name    : BoundedEntropyGames.ConvRate.eq_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:33.59709+00:00
-- url     : https://prove2.me/theorems/c0756d03-d667-4f26-a08d-61334ecbef10
-- title:
--   (A.5), p. 38 — the random-mapping operator bound for $\alpha\in[1,2]$
-- statement:
--   Let $p_A$ be a pmf on finite $\mathcal A$ and $p_F$ the law of the random mapping $F:\mathcal X\to\mathcal A$ with i.i.d. values of law $p_A$. For every $\alpha\in[1,2]$, every real function $g:\mathcal X\to\mathbb R$ and every $a\in\mathcal A$,
--   $$
--   \sum_{f}p_F(f)\Big|\sum_{x}g(x)\big(\mathbb 1(f(x)=a)-p_A(a)\big)\Big|^\alpha\le 2^{2-\alpha}p_A(a)\sum_x|g(x)|^\alpha .
--   $$
--
--   Applied to $g=p_{X|Y}(\cdot|y)$ and combined with Jensen's inequality, this yields the simulation bound (14) of Lemma 14.
--
--   **Formalization Note** Powers with exponent $\alpha$ are real powers of nonnegative numbers.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 38, Appendix A, (A.5)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (A.5), p. 38: for every `α ∈ [1, 2]`, every real `g : 𝒳 → ℝ` and every `a ∈ 𝒜`,
`∑_f p_F(f) |∑_x g(x)(𝟙(f(x) = a) - p_A(a))|^α ≤ 2^{2-α} p_A(a) ∑_x |g(x)|^α`. -/
theorem eq_A_5 {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) :
    ∀ α ∈ Set.Icc (1 : ℝ) 2, ∀ (g : 𝒳 → ℝ) (a : 𝒜),
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ α
        ≤ (2 : ℝ) ^ (2 - α) * pA a * ∑ x, |g x| ^ α := by sorry

end BoundedEntropyGames.ConvRate
