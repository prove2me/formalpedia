-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_theorem_2_4
-- name    : ConvexOptAlg.Ellipsoid.theorem_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:31:58.474674+00:00
-- url     : https://prove2.me/theorems/a1aa416e-29ef-4bff-bb4b-ed913de72b3f
-- title:
--   Theorem 2.4, p. 250 — for t ≥ 2n² log(R/r) the ellipsoid method hits X and f(x_t) − min_X f ≤ (2BR/r)·exp(−t/(2n²))
-- statement:
--   Let $n\ge2$ and let $\mathcal X\subset\mathbb R^n$ be a convex body (compact, convex, with non-empty interior). Let $f$ be continuous and convex on $\mathcal X$ with values in $[-B,B]$, and let $x^*\in\mathcal X$ be a minimizer of $f$ on $\mathcal X$. Let $r,R>0$ be such that $\mathcal X$ is contained in the Euclidean ball $\mathcal E_0$ of center $c_0$ and radius $R$ and contains a Euclidean ball of radius $r$. Consider any run $(c_t,H_t,w_t)_{t\ge0}$ of the ellipsoid method started from $\mathcal E_0$ (so $H_0=R^2\mathrm I_n$). Then for every integer $t\ge1$ with
--
--   $$
--   t\ \ge\ 2n^2\log(R/r),
--   $$
--
--   1. some center among $c_0,\dots,c_{t-1}$ lies in $\mathcal X$, and
--   2. every $x_t\in\operatorname{argmin}\{f(c):c\in\{c_0,\dots,c_{t-1}\}\cap\mathcal X\}$ satisfies
--   $$
--   f(x_t)-\min_{x\in\mathcal X}f(x)\ \le\ \frac{2BR}{r}\exp\Big(-\frac{t}{2n^2}\Big).
--   $$
--
--   The ellipsoid method thus reaches accuracy $\varepsilon$ after $O(n^2\log(1/\varepsilon))$ oracle calls, each followed by an update costing $O(n^2)$ arithmetic operations; this is what makes it a polynomial-time method whenever a separation oracle is available.
--
--   **Formalization Note**
--   1. $\mathbb R^n$ is `Fin n → ℝ`; balls are Euclidean, written with the dot product.
--   2. $n\ge2$ is added because the update (2.6) contains $n^2/(n^2-1)$ and is defined only for $n\ge2$ (Lemma 2.3 gives it for $n\ge2$).
--   3. The existence of $x^*$ is the book's standing assumption (p. 242).
--   4. The page writes $\{c_1,\dots,c_t\}$; the centers queried during $t$ iterations, whose cuts produce $\mathcal E_t$, are $c_0,\dots,c_{t-1}$, and the statement uses these.
--   5. $t\ge1$ is added: when $R=r$ the threshold is $t\ge0$, and at $t=0$ no center has been queried, so the nonemptiness claim would fail.
--   6. When an oracle answer is $w_s=0$ (only possible at a minimizer $c_s\in\mathcal X$) the run stops, as described in the definition module; the bound then holds trivially for $t>s$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 2.4, p. 250 (method pp. 249–250, chapter setting p. 244)

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- **Theorem 2.4** (Bubeck, arXiv:1405.4980v2, p. 250). Let `n ≥ 2`, `X ⊂ ℝⁿ` a convex body,
`f : X → [−B, B]` continuous and convex with a minimizer `x∗` on `X`, and `r, R > 0` with
`X` inside the Euclidean ball of center `c₀` and radius `R` and containing a Euclidean ball of
radius `r`. For every run of the ellipsoid method from `E₀ = B(c₀, R)` and every
`t ≥ 2n² log(R/r)` with `t ≥ 1`: some center queried in the first `t` iterations
(`c₀, …, c_{t−1}`) lies in `X`, and every output `x_t` (a minimizer of `f` over those centers
in `X`) satisfies `f(x_t) − min_X f ≤ (2BR/r) exp(−t/(2n²))`.

Indexing: the page writes `{c₁, …, c_t}`; the centers queried in `t` iterations, whose cuts
produce `E_t`, are `c₀, …, c_{t−1}`. -/
theorem theorem_2_4 {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    (B : ℝ) (hfB : ∀ x ∈ X, -B ≤ f x ∧ f x ≤ B)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (c0 : Fin n → ℝ) (hXR : X ⊆ euclBall c0 R)
    (z : Fin n → ℝ) (hXr : euclBall z r ⊆ X)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (c : ℕ → Fin n → ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : 2 * (n : ℝ) ^ 2 * Real.log (R / r) ≤ (t : ℝ)) :
    (∃ s < t, c s ∈ X) ∧
      ∀ x : Fin n → ℝ, IsEllipsoidOutput X f c t x →
        f x - f xstar ≤ 2 * B * R / r * Real.exp (-(t : ℝ) / (2 * (n : ℝ) ^ 2)) := by sorry

end ConvexOptAlg.Ellipsoid
