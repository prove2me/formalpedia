-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_E_2
-- name    : AdaDiscRL.lemma_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:48.570982+00:00
-- url     : https://prove2.me/theorems/298098be-0d15-4d8e-bee1-c646e25ec5f2
-- title:
--   Lemma E.2 — clipping to the gap (corrected: $\mu_2\ge0$)
-- statement:
--   Let $H\ge1$ and let $g,\varphi,\mu_1,\mu_2$ be real numbers with $\mu_2\ge0$. If $g\le\varphi\le\mu_1+\mu_2$, then
--   $$
--   \varphi\le\mathrm{clip}\Big[\mu_1\ \Big|\ \frac{g}{H+1}\Big]+\Big(1+\frac1H\Big)\mu_2 ,
--   $$
--   where $\mathrm{clip}[\mu\mid\nu]=\mu\,\mathbb 1[\mu\ge\nu]$. In the paper $g=\mathrm{gap}_h(B)$; the lemma lets the regret analysis drop confidence terms below the gap threshold at the price of a factor $1+1/H$ on the downstream error.
--
--   Differences from the source:
--   - correction: for any quantities φ, μ₁, μ₂ → μ₂ ≥ 0; reason: g = φ = 0, μ₁ = 1, μ₂ = −1 satisfy g ≤ φ ≤ μ₁ + μ₂ but 0 ≤ 1 − (1 + 1/H) fails (correction C8); every use has μ₂ = f ≥ 0 by optimism
--   - generalization: gap_h(B) → any real g; reason: gap_h(B) is one real number
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma E.2, p.48

import Mathlib
import Definitions.Def_AdaDiscRL_clip

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma E.2 (Clipping to the Gap)** (arXiv:2110.15843v3, p.48), corrected. If
`gap_h(B) ≤ φ ≤ μ₁ + μ₂` and `μ₂ ≥ 0`, then `φ ≤ clip[μ₁ | gap_h(B)/(H + 1)] + (1 + 1/H) μ₂`, where
`clip[μ | ν] = μ 1[μ ≥ ν]`.

**Formalization Note.** `g` stands for `gap_h(B)`; any real `g` is allowed. Correction: `0 ≤ μ₂` is
added ("for any quantities" fails at `g = φ = 0`, `μ₁ = 1`, `μ₂ = −1`: `0 ≤ 1 − (1 + 1/H)` is false);
every use has `μ₂ = f ≥ 0` by optimism. `H ≥ 1`. -/
theorem lemma_E_2 (H : ℕ) (hH : 1 ≤ H) (g φ μ₁ μ₂ : ℝ) (hμ₂ : 0 ≤ μ₂) (hg : g ≤ φ) (hφ : φ ≤ μ₁ + μ₂) :
    φ ≤ clip μ₁ (g / ((H : ℝ) + 1)) + (1 + 1 / (H : ℝ)) * μ₂ := by sorry

end AdaDiscRL
