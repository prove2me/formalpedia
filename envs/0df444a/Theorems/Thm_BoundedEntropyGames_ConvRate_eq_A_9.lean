-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_A_9
-- name    : BoundedEntropyGames.ConvRate.eq_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:36.725781+00:00
-- url     : https://prove2.me/theorems/3d2a97ab-19da-4f46-90d5-f1ad7b6566a3
-- title:
--   (A.8)–(A.9), p. 40 — the case $\alpha=1$ of (A.5)
-- statement:
--   Let $p_A$ be a pmf on finite $\mathcal A$, let $F:\mathcal X\to\mathcal A$ be the random mapping with i.i.d. values of law $p_A$ (law $p_F$), let $g:\mathcal X\to\mathbb R$ be any real function and $a\in\mathcal A$. Then
--   $$
--   \sum_{f}p_F(f)\Big|\sum_{x}g(x)\big(\mathbb 1(f(x)=a)-p_A(a)\big)\Big|\le 2p_A(a)(1-p_A(a))\sum_x|g(x)|\le 2p_A(a)\sum_x|g(x)|.
--   $$
--
--   This is the $L^1$ endpoint of the interpolation that proves (A.5) and hence Lemma 14.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 40, Appendix A, (A.8)–(A.9)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (A.8)–(A.9), p. 40: the case `α = 1` of (A.5). -/
theorem eq_A_9 {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (g : 𝒳 → ℝ) (a : 𝒜) :
    ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
        ≤ 2 * pA a * (1 - pA a) * ∑ x, |g x| ∧
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
        ≤ 2 * pA a * ∑ x, |g x| := by sorry

end BoundedEntropyGames.ConvRate
