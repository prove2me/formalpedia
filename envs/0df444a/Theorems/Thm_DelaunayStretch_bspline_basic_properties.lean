-- Prove2me | Theorems.Thm_DelaunayStretch_bspline_basic_properties
-- name    : DelaunayStretch.bspline_basic_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:24:41.569038+00:00
-- url     : https://prove2.me/theorems/57bbfa8c-cc53-4af7-8c3c-a09398f22bc1
-- title:
--   Clamped cubic B-splines: nonnegative, partition of unity, piecewise cubic, $C^2$
-- statement:
--   Let $N_0,\dots,N_{34}$ be the clamped uniform cubic B-splines on $[0,1]$ with knots $(0,0,0,0,\tfrac1{32},\tfrac2{32},\dots,\tfrac{31}{32},1,1,1,1)$, defined by the Cox–de Boor recursion with the last knot interval closed (Definition 5.2). Then:
--
--   1. $N_l(\tau)\ge0$ for all $\tau\in[0,1]$;
--   2. $\displaystyle\sum_{l=0}^{34}N_l(\tau)=1$ for all $\tau\in[0,1]$;
--   3. on every knot interval $[\tfrac{i}{32},\tfrac{i+1}{32}]$, $0\le i\le31$, each $N_l$ coincides with a polynomial of degree at most $3$;
--   4. the B-splines extended to $\tau<0$ by the cubic polynomial they equal on $[0,\tfrac1{32}]$ (Definition 5.5) are twice continuously differentiable on $(-\infty,1)$.
--
--   These are the standard properties of B-splines recalled in Definition 5.2 and used in the proof of Lemma 5.6. The family $\mathcal H$ is designed around them: a function is bounded by its largest B-spline coefficient, and every coefficient function is a polynomial in $\tau$ between consecutive knots.
--
--   **Formalization Note** The statement is about the platform definitions `bspline` (Cox–de Boor, with $0/0=0$ for repeated knots) and `bsplineExt` (Definition 5.5 extension). The first three items quantify over all $l\in\mathbb N$; for $l\ge35$ the recursion gives the zero function.
-- source:
--   Mo, Cheng, Ding, arXiv:2609.07979v6, Definition 5.2 (p.31: 'they are 35 nonnegative functions that sum to 1, twice continuously differentiable on [0,1], and each of them is a cubic polynomial between consecutive knots'), Definition 5.5 and proof of Lemma 5.6 (pp.34–35); standard B-spline theory [dB01]

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces

namespace DelaunayStretch

/-- **The clamped cubic B-splines** (Definition 5.2, p.31, and the proof of Lemma 5.6, p.35):
`N₀, …, N₃₄` are nonnegative on `[0, 1]` and sum to `1` there; each is a polynomial of degree at
most `3` on every knot interval `[i/32, (i+1)/32]`; and the B-splines extended to `τ < 0` by the
cubic on `[0, 1/32]` (Definition 5.5) are twice continuously differentiable on `(−∞, 1)`. -/
theorem bspline_basic_properties :
    (∀ (l : ℕ) (τ : ℝ), 0 ≤ τ → τ ≤ 1 → 0 ≤ bspline l τ) ∧
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∑ l : Fin 35, bspline l τ = 1) ∧
    (∀ (l i : ℕ), i < 32 → ∃ p : Polynomial ℝ, p.natDegree ≤ 3 ∧
      ∀ τ ∈ Set.Icc ((i : ℝ) / 32) (((i : ℝ) + 1) / 32), bspline l τ = p.eval τ) ∧
    (∀ l : ℕ, ContDiffOn ℝ 2 (bsplineExt l) (Set.Iio 1)) := by sorry

end DelaunayStretch
