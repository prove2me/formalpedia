-- Prove2me | Theorems.Thm_CongestionTaxes_c_convex
-- name    : CongestionTaxes.c_convex
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:32:42.643239+00:00
-- url     : https://prove2.me/theorems/57547efc-2246-4ba3-929f-83458f4d2e8b
-- title:
--   Footnote 4 and p.28 (corrected: $\ge 0$ for $>0$) — $c(x)=x\ell(x)$ is convex on $\mathbb N_0$
-- statement:
--   Let $\ell$ satisfy Assumption 1, extended by $\ell(0)=0$, and let $c(x)=x\ell(x)$. Then $c$ is convex on $\mathbb N_0$:
--
--   $$
--   c(x+2)+c(x)\ \ge\ 2\,c(x+1)\qquad\text{for all }x\in\mathbb N_0 .
--   $$
--
--   At $x=0$ this reads $2\ell(2)\ge2\ell(1)$, which is non-decreasingness; for $x\ge1$ it is semi-convexity (footnote 4). Convexity of $c$ including the step at $1$ is what Lemma 4 (convexity of $p$) and the corrected Lemma 5 use.
--
--   Differences from the source:
--
--   - correction: p.28: $c(2)-2c(1)=2(\ell(2)-\ell(1))>0$ → $c(2)-2c(1)\ge0$; reason: non-decreasingness gives only $\ge$; for $\ell=1$ on $\mathbb N$ (Assumption 1 holds) $c(2)-2c(1)=0$, and the proof needs only $\ge0$
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, footnote 4, p.5; proof of Lemma 4, p.28

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1

namespace CongestionTaxes

/-- Paccagnan, Gairing, arXiv:2105.07480v2, footnote 4, p.5, and the proof of Lemma 4, p.28:
under Assumption 1, `c(x) = x ℓ(x)` with `c(0) = 0` is convex on `ℕ₀`,
`c(x + 2) + c(x) ≥ 2 c(x + 1)` for every `x ∈ ℕ₀`. At `x = 0` this is `2ℓ(2) ≥ 2ℓ(1)`
(non-decreasingness, p.28: "c(2) − 2c(1) = 2(ℓ(2) − ℓ(1))"); for `x ≥ 1` it is semi-convexity.

**Formalization Note** `c` is written out as `x * ℓ x`; casts are real. -/
theorem c_convex (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (x : ℕ) :
    2 * (((x : ℝ) + 1) * ℓ (x + 1)) ≤ ((x : ℝ) + 2) * ℓ (x + 2) + (x : ℝ) * ℓ x := by sorry

end CongestionTaxes
