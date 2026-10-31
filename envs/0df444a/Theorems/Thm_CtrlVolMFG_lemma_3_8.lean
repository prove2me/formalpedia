-- Prove2me | Theorems.Thm_CtrlVolMFG_lemma_3_8
-- name    : CtrlVolMFG.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:13.298526+00:00
-- url     : https://prove2.me/theorems/ab07c595-42df-4c5e-b960-02922e0610ab
-- title:
--   Lemma 3.8 — $C$-displacement monotonicity projected onto empirical measures
-- statement:
--   Suppose that $U=U(x,m):\mathbb R^n\times\mathcal P_2(\mathbb R^n)\to\mathbb R$ is $C$-displacement monotone, $C\in\mathbb R$. Then for any $\mathbf x=(x^1,\dots,x^N)$, $\bar{\mathbf x}=(\bar x^1,\dots,\bar x^N)\in(\mathbb R^n)^N$,
--   $$\sum_{i=1}^N\big(D_xU(x^i,m^N_{\mathbf x})-D_xU(\bar x^i,m^N_{\bar{\mathbf x}})\big)\cdot(x^i-\bar x^i)\ge C\sum_{i=1}^N|x^i-\bar x^i|^2.$$
--
--   The lemma transfers displacement monotonicity, a condition on random variables, to the finite systems of the $N$-player game.
--
--   Differences from the source:
--   - reading: $U:\mathbb R^n\times\mathcal P_2(\mathbb R^n)\to\mathbb R^n$ → $U$ real valued; reason: $D_xU$ is paired with $x^i-\bar x^i$ and the lemma is applied to $G$ and $F$, which are real valued
--   - encoding: "for any square-integrable random variables" in (1.6), (2.16), (2.19) → for every coupling $\pi$ with finite second moments, the laws being the marginals of $\pi$, whenever the integrand is integrable; reason: random variables enter only through their joint law, and every coupling is a joint law on an atomless space
--   - encoding: $N\in\mathbb N$ → any $N\ge0$; reason: for $N=0$ both sides are $0$
--   - encoding: players $i\in\{1,\dots,N\}$ → players `i : Fin N`, player $i$ of the paper is index $i-1$; reason: relabelling
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, Lemma 3.8, p.22; (1.6) p.3

import Mathlib
import Definitions.Def_CtrlVolMFG_IsSol_3_6

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

/-- Lemma 3.8 (Jackson & Tangpi, arXiv:2304.04543v2, p.22): if `U : ℝⁿ × 𝒫₂(ℝⁿ) → ℝ` is
`C`-displacement monotone, then for any `x = (x¹, …, xᴺ)`, `x̄ = (x̄¹, …, x̄ᴺ) ∈ (ℝⁿ)ᴺ`,
`∑ᵢ (D_xU(xⁱ, m^N_x) − D_xU(x̄ⁱ, m^N_x̄))·(xⁱ − x̄ⁱ) ≥ C ∑ᵢ |xⁱ − x̄ⁱ|²`.

**Formalization Note** The page types `U` as `ℝⁿ`-valued; it is real-valued (`D_xU` is paired
with `xⁱ − x̄ⁱ`). `C` is any real number. -/
theorem lemma_3_8 {n : ℕ} (U : Rn n → P2 n → ℝ) (C : ℝ) (hU : IsDisplMono C U) (N : ℕ)
    (x x' : Fin N → Rn n) :
    C * ∑ i, ‖x i - x' i‖ ^ 2 ≤
      ∑ i, inner ℝ (Dx U (x i) (empP2 x) - Dx U (x' i) (empP2 x')) (x i - x' i) := by sorry

end CtrlVolMFG
