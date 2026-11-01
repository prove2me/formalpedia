-- Prove2me | Theorems.Thm_CongestionTaxes_lemma_5
-- name    : CongestionTaxes.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:43.240472+00:00
-- url     : https://prove2.me/theorems/d4fbab19-148e-437e-ae8b-fe5aa8df87c9
-- title:
--   Lemma 5 (corrected: convexity on $\mathbb N_0$) — $g(x,v)$ is non-decreasing in $x$
-- statement:
--   Let $c:\mathbb N_0\to\mathbb R_{\ge0}$ with $c(0)=0$ be convex on $\mathbb N_0$, i.e. $c(x+2)+c(x)\ge2c(x+1)$ for all $x\ge0$. Then for every fixed $v>0$ the function
--
--   $$
--   g(x,v)=\frac{\sum_{i=1}^{x}\frac{x\,c(i)-i\,c(i-1)}{i!}v^i}{\sum_{i=0}^{x}\frac{x-i}{i!}v^i}
--   $$
--
--   is non-decreasing in $x\in\mathbb N$: $g(x+1,v)\ge g(x,v)$ for all $x\ge1$.
--
--   This is the technical step that makes the modified costs of Definition 4 non-decreasing (Lemma 1(b)).
--
--   Differences from the source:
--
--   - correction: $c:\mathbb N\to\mathbb R_{\ge0}$ convex (on $\mathbb N$, footnote 4 starts at $x=2$), $c(0)=0$ → convexity on $\mathbb N_0$: $c(x+2)+c(x)\ge2c(x+1)$ for all $x\ge0$; reason: as printed the lemma is false: $c(x)=1$ for $x\ge1$, $c(0)=0$ gives $g(1,1)=1>2/3=g(2,1)$; the proof's last step uses that $b$ is non-decreasing, which is the step at $1$; $c(x)=x\ell(x)$ under Assumption 1 satisfies the corrected hypothesis (`c_convex`)
--   - encoding: $g$ non-decreasing for all $x\in\mathbb N$ → $g(x,v)\le g(x+1,v)$ for $x\ge1$; reason: equivalent
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Lemma 5, p.30

import Mathlib
import Definitions.Def_CongestionTaxes_gRatio

namespace CongestionTaxes

/-- **Lemma 5, corrected** (Paccagnan, Gairing, arXiv:2105.07480v2, Lemma 5, p.30). Let
`c : ℕ₀ → ℝ≥0` with `c(0) = 0` be convex on `ℕ₀`: `c(x + 2) + c(x) ≥ 2c(x + 1)` for all `x ≥ 0`.
Then for every fixed `v > 0`, `x ↦ g(x, v)` is non-decreasing on `ℕ`:
`g(x + 1, v) ≥ g(x, v)` for all `x ≥ 1`, where
`g(x, v) = (∑_{i=1}^x ((x c(i) − i c(i−1)) / i!) vⁱ) / (∑_{i=0}^x ((x − i) / i!) vⁱ)`.

**Formalization Note** The printed lemma asks for convexity on `ℕ` only (footnote 4 starts at
`x = 2`) and is then false: `c(x) = 1` for `x ≥ 1`, `c(0) = 0` gives `g(1, 1) = 1 > 2/3 = g(2, 1)`.
Convexity is therefore required on `ℕ₀`, including the step at `1`; this holds for
`c(x) = x ℓ(x)` under Assumption 1 (`c_convex`), the lemma's only use. -/
theorem lemma_5 (c : ℕ → ℝ) (h0 : c 0 = 0) (hnn : ∀ x, 0 ≤ c x)
    (hconv : ∀ x : ℕ, 2 * c (x + 1) ≤ c (x + 2) + c x) (v : ℝ) (hv : 0 < v) (x : ℕ)
    (hx : 1 ≤ x) : gRatio c x v ≤ gRatio c (x + 1) v := by sorry

end CongestionTaxes
