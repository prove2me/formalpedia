-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_ball_subset_hull_of_kkt
-- name    : ConvexOptimization.lowner_john_ball_subset_hull_of_kkt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:11:11.236394+00:00
-- url     : https://prove2.me/theorems/6a745f25-81cd-452c-9e84-e527a1c72afc
-- title:
--   The $1/n$ ball lies in the hull
-- statement:
--   The geometric core of Löwner–John rounding: a John decomposition of the identity forces the ball of radius $1/n$ to lie inside the convex hull of the points.
--
--   Let $n \ge 1$, let $x_1,\dots,x_m \in \mathbb{R}^n$, and let $\lambda_1,\dots,\lambda_m \ge 0$ satisfy the normalized optimality identities
--
--   $$\sum_{i=1}^{m} \lambda_i\, x_i x_i^{T} = I, \qquad \sum_{i=1}^{m} \lambda_i\, x_i = 0, \qquad \lambda_i\bigl(1 - x_i^{T} x_i\bigr) = 0 \quad (i = 1,\dots,m),$$
--
--   where $x_i x_i^{T}$ is the rank-one outer product and $I$ the $n \times n$ identity; the third family is complementary slackness, so every $x_i$ carrying a nonzero weight lies on the unit sphere. Then every $v \in \mathbb{R}^n$ whose Euclidean norm satisfies $\lVert v \rVert_2 \le 1/n$, i.e. $v^{T} v \le 1/n^{2}$, lies in the hull of the points:
--
--   $$\{\, v \in \mathbb{R}^n : \lVert v\rVert_2 \le 1/n \,\} \;\subseteq\; \operatorname{conv}\{x_1,\dots,x_m\}.$$
--
--   This is the step that produces the dimension-dependent constant in Löwner–John rounding, and it is stated separately from the optimization problem so that it applies to *any* family satisfying a John decomposition of the identity, whatever its origin — the same statement is the workhorse behind John's theorem in Banach-space geometry. The constant is sharp: for the regular simplex inscribed in the unit sphere, the largest centred ball inside the simplex has radius exactly $1/n$.
--
--   **Formalization Note** Both norms are written through the dot product `⬝ᵥ` on `Fin n → ℝ`, so the hypothesis on $v$ reads `v ⬝ᵥ v ≤ 1 / n ^ 2`; the dimension is called `nn` and is assumed positive. The fourth KKT identity $\sum_i \lambda_i = n$ is *not* needed and is deliberately absent from the hypotheses. Source: Boyd & Vandenberghe §8.4.1, pp. 412–413.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 412-413, §8.4.1 (the convex-combination step that produces the ball of radius 1/n)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_ball_subset_hull_of_kkt {nn m : ℕ} (hnn : 0 < nn)
    (x : Fin m → Fin nn → ℝ) (lam : Fin m → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hI : (∑ i, lam i • Matrix.vecMulVec (x i) (x i)) = (1 : Matrix (Fin nn) (Fin nn) ℝ))
    (hz : (∑ i, lam i • x i) = 0)
    (hcs : ∀ i, lam i * (1 - x i ⬝ᵥ x i) = 0)
    (v : Fin nn → ℝ) (hv : v ⬝ᵥ v ≤ 1 / (nn : ℝ) ^ 2) :
    v ∈ convexHull ℝ (Set.range x) := by
  sorry
