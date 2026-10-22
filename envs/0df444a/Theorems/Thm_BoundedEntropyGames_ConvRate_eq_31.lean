-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_31
-- name    : BoundedEntropyGames.ConvRate.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:04.992469+00:00
-- url     : https://prove2.me/theorems/aff5eed8-8a4e-4480-b871-44ba76a6c7a6
-- title:
--   (31), p. 23 — the per-block simulation bound $\delta_n$
-- statement:
--   Let $p_{XY}$, $r\in(0,1]$, $p^{(1)}_A,p^{(2)}_A$ satisfy (19) and (20), and $\beta=H(p^{(1)}_A)-H(p^{(2)}_A)$. There is $\gamma\ge0$ with the following property. For all integers $1\le f\le n$, all $g\in[0,r]$, all $h\in(0,1]$ and all block lengths $N\le N'$ with $N\ge n/f-1$, let $m=\lfloor N(r-g)\rfloor$ and let $q$ be the ideal block law (22) on $\mathcal A^N$. Then there is a map $\varphi:\mathcal X^{N'}\to\mathcal A^N$ such that, for $(X^{N'},Y^{N'})$ i.i.d. from $p_{XY}$,
--   $$
--   \big\|p_{\varphi(X^{N'})\,Y^{N'}}-q\,p_{Y^{N'}}\big\|_{TV}\le 2^{-\frac12\left(\frac nf-1\right)h\,(\beta g-\gamma h)} .
--   $$
--
--   In the proof of Theorem 6 this is applied with $f=f_n$, $g=g_n$, $h=h_n$, $N=N_{n,i}$, $N'=N_{n,i-1}$, and $\varphi=\varphi_i$ is Alice's block map; the right side is $\delta_n$.
--
--   **Formalization Note** The hypothesis $f\le n$ is added: when $f>n$ and $\beta g<\gamma h$ the right side can be smaller than one while the total variation is not, so the inequality is meant for $n/f-1\ge0$, the only case in which the paper's blocks are nonempty. In Theorem 6 the case $f_n>n$ is covered by the term $f_n/n$. $\gamma$ is existential for the reason given in (29).
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 23, (31) (with (22)–(26), (29)–(30), pp. 21–23)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (31), p. 23: the per-block simulation bound. Under (19), (20) and `0 < r ≤ 1`, with
`β = H(p^(1)) - H(p^(2))`, there is `γ ≥ 0` such that for all `1 ≤ f ≤ n`, `0 ≤ g ≤ r`,
`0 < h ≤ 1` and block lengths `N ≤ N'` with `N ≥ n/f - 1`, some map `φ : 𝒳^{N'} → 𝒜^N`
makes the law of `(φ(X^{N'}), Y^{N'})` `δ`-close to `q ⊗ p_{Y^{N'}}`, where `q` is the ideal
block law (22) with `m = ⌊N(r - g)⌋` and `δ = 2^{-½(n/f - 1)h(βg - γh)}`. -/
theorem eq_31 {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1)
    (p₁ p₂ : 𝒜 → ℝ) (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (h19 : r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY)
    (h20 : shannon p₂ < shannon p₁) :
    ∃ γ ≥ (0 : ℝ), ∀ n f : ℕ, 1 ≤ f → f ≤ n → ∀ g ∈ Set.Icc (0 : ℝ) r,
      ∀ h ∈ Set.Ioc (0 : ℝ) 1, ∀ N N' : ℕ, N ≤ N' → (n : ℝ) / f - 1 ≤ N →
        ∃ φ : (Fin N' → 𝒳) → (Fin N → 𝒜),
          tv (pfXY (iidJoint pXY N') φ)
              (fun z => idealBlock p₁ p₂ ⌊(N : ℝ) * (r - g)⌋₊ N z.1 *
                marginalY (iidJoint pXY N') z.2)
            ≤ (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f - 1) * h *
                ((shannon p₁ - shannon p₂) * g - γ * h)) := by sorry

end BoundedEntropyGames.ConvRate
