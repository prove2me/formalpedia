-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_29
-- name    : BoundedEntropyGames.ConvRate.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:38.213993+00:00
-- url     : https://prove2.me/theorems/3699d673-c55e-436f-9b47-e5238a6550c0
-- title:
--   (28)–(29), p. 22 — the entropy-gap inequality
-- statement:
--   Let $p_{XY}$ be a joint pmf, $r\in(0,1]$, and $p^{(1)}_A,p^{(2)}_A$ pmfs on $\mathcal A$ with
--   $rH(p^{(1)}_A)+(1-r)H(p^{(2)}_A)\le H(X|Y)$ (19) and $H(p^{(1)}_A)>H(p^{(2)}_A)$ (20). Put $\beta=H(p^{(1)}_A)-H(p^{(2)}_A)>0$. There is $\gamma\ge0$ such that for every $\alpha\in(1,2]$, every $g\in[0,r]$ and every $\rho\in[0,r-g]$,
--   $$
--   H_\alpha(X|Y)-\rho H_{1/\alpha}(p^{(1)}_A)-(1-\rho)H_{1/\alpha}(p^{(2)}_A)\ge\beta g-\gamma(\alpha-1).
--   $$
--
--   In the proof of Theorem 6, $g=g_n$ and $\rho=r_{n,i}=m_{n,i}/N_{n,i}\le r-g_n$; the inequality makes the exponent of the per-block simulation bound positive.
--
--   **Formalization Note** The paper defines $\gamma=2\max\{d_1(X|Y)+\max\{d_1(p^{(1)}_A),d_1(p^{(2)}_A)\},\ d_2(X|Y)+\max\{d_2(p^{(1)}_A),d_2(p^{(2)}_A)\}\}$. Because $d_2$ is replaced by existential constants in (3)–(6), $\gamma$ is existential here, depending only on $p_{XY},p^{(1)}_A,p^{(2)}_A$. $\alpha=1$ is excluded (the Rényi formula is undefined there).
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 22, (28)–(29)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (28)–(29), p. 22: under (19), (20) and `0 < r ≤ 1`, with `β = H(p^(1)) - H(p^(2))`, there
is `γ ≥ 0` such that for `α ∈ (1, 2]`, `0 ≤ g ≤ r` and `0 ≤ ρ ≤ r - g` (`ρ` plays
`r_{n,i}`), `H_α(X|Y) - ρ H_{1/α}(p^(1)) - (1-ρ) H_{1/α}(p^(2)) ≥ β g - γ (α - 1)`. -/
theorem eq_29 {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [Fintype 𝒳] [Fintype 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1)
    (p₁ p₂ : 𝒜 → ℝ) (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (h19 : r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY)
    (h20 : shannon p₂ < shannon p₁) :
    ∃ γ ≥ (0 : ℝ), ∀ α ∈ Set.Ioc (1 : ℝ) 2, ∀ g ∈ Set.Icc (0 : ℝ) r, ∀ ρ ∈ Set.Icc (0 : ℝ) (r - g),
      (shannon p₁ - shannon p₂) * g - γ * (α - 1)
        ≤ condRenyi α pXY - ρ * renyi (1 / α) p₁ - (1 - ρ) * renyi (1 / α) p₂ := by sorry

end BoundedEntropyGames.ConvRate
