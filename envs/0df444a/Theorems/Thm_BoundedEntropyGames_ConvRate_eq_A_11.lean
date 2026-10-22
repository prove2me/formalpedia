-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_A_11
-- name    : BoundedEntropyGames.ConvRate.eq_A_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:30.71601+00:00
-- url     : https://prove2.me/theorems/4e8fb810-2693-45fe-9a74-24be952b67f2
-- title:
--   (A.10)–(A.11), p. 41 — the case $\alpha=2$ of (A.5)
-- statement:
--   Let $p_A$ be a pmf on finite $\mathcal A$, $p_F$ the law of the random mapping $F:\mathcal X\to\mathcal A$ with i.i.d. values of law $p_A$, $g:\mathcal X\to\mathbb R$ and $a\in\mathcal A$. Then
--   $$
--   \sum_f p_F(f)\Big|\sum_x g(x)\big(\mathbb 1(f(x)=a)-p_A(a)\big)\Big|^2=p_A(a)(1-p_A(a))\sum_x g(x)^2\le p_A(a)\sum_x g(x)^2 .
--   $$
--
--   This is the $L^2$ endpoint of the interpolation that proves (A.5).
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 41, Appendix A, (A.10)–(A.11)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (A.10)–(A.11), p. 41: the case `α = 2` of (A.5). -/
theorem eq_A_11 {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (g : 𝒳 → ℝ) (a : 𝒜) :
    ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
        = pA a * (1 - pA a) * ∑ x, g x ^ 2 ∧
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ 2
        ≤ pA a * ∑ x, g x ^ 2 := by sorry

end BoundedEntropyGames.ConvRate
