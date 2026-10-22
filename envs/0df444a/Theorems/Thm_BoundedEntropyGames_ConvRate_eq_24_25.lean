-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_24_25
-- name    : BoundedEntropyGames.ConvRate.eq_24_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:49.418629+00:00
-- url     : https://prove2.me/theorems/7ec71d97-7651-43a1-95be-c905ae9ddb4d
-- title:
--   (24)–(25), p. 21 — Rényi entropy of the ideal block law and of an i.i.d. source
-- statement:
--   1. Let $p^{(1)},p^{(2)}$ be pmfs on finite $\mathcal A$, $m\le N$ integers, and $q$ the ideal block law (22) on $\mathcal A^N$ ($m$ i.i.d. draws from $p^{(1)}$ followed by $N-m$ from $p^{(2)}$). For every order $\beta>0$, $\beta\ne1$,
--   $$
--   H_\beta(q)=mH_\beta(p^{(1)})+(N-m)H_\beta(p^{(2)}).
--   $$
--   2. Let $p_{XY}$ be a joint pmf and $(X^{N'},Y^{N'})$ be $N'$ i.i.d. copies. For every $\alpha>0$, $\alpha\ne1$, and $N\le N'$,
--   $$
--   H_\alpha(X^{N'}|Y^{N'})=N'H_\alpha(X|Y)\ge NH_\alpha(X|Y).
--   $$
--
--   The paper applies part 1 at order $\beta=1/\alpha$ with $m=m_{n,i}$, $N=N_{n,i}$, and part 2 with $N'=N_{n,i-1}\ge N=N_{n,i}$.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 21, (24)–(25)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (24)–(25), p. 21: the Rényi entropy of the ideal block law (22) is additive over its
stages, and the conditional Rényi entropy of `N'` i.i.d. copies of `(X, Y)` is `N'` times
that of one copy, hence at least `N` times it when `N ≤ N'`. The paper applies (24) at
order `β = 1/α`. -/
theorem eq_24_25 {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴] :
    (∀ (p₁ p₂ : 𝒜 → ℝ), IsPMF p₁ → IsPMF p₂ → ∀ (m N : ℕ), m ≤ N →
      ∀ β : ℝ, 0 < β → β ≠ 1 →
        renyi β (idealBlock p₁ p₂ m N) = m * renyi β p₁ + ((N : ℝ) - m) * renyi β p₂) ∧
    (∀ (pXY : 𝒳 × 𝒴 → ℝ), IsPMF pXY → ∀ (N N' : ℕ), N ≤ N' →
      ∀ α : ℝ, 0 < α → α ≠ 1 →
        condRenyi α (iidJoint pXY N') = N' * condRenyi α pXY ∧
          (N : ℝ) * condRenyi α pXY ≤ N' * condRenyi α pXY) := by sorry

end BoundedEntropyGames.ConvRate
