-- Prove2me | Theorems.Thm_CaiCandesShen_GeneralConvex_optimal_dual_fixed_point
-- name    : CaiCandesShen.GeneralConvex.optimal_dual_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:20:10.88221+00:00
-- url     : https://prove2.me/theorems/6768bb70-a8d0-4afa-9a4d-f7b7937977cf
-- title:
--   Lemma 4.3 — $y^\star = [y^\star + \delta\mathcal F(X^\star)]_+$ for every $\delta>0$
-- statement:
--   Let $\tau>0$, let $f_1,\dots,f_m$ be convex functions on $\mathbb R^{n_1\times n_2}$, $\mathcal F = (f_1,\dots,f_m)$, and let $(X^\star, y^\star)$ be a primal-dual optimal pair (saddle point of the Lagrangian $\mathcal L(X,y) = f_\tau(X) + \langle y,\mathcal F(X)\rangle$ over $X$ and $y\ge 0$) for problem (3.4). Then for each $\delta>0$,
--   $$y^\star = [\,y^\star + \delta\,\mathcal F(X^\star)\,]_+ ,$$
--   where the positive part is taken entrywise.
--
--   In words, the optimal multiplier is a fixed point of the projected dual step; this is the complementary slackness relation that makes the dual iteration of (3.5) stationary at the optimum.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1969, Lemma 4.3, Eq. (4.3)

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Lemma 4.3, p. 1969: if `(X⋆, y⋆)` is a primal-dual optimal pair for (3.4), then for each
`δ > 0`, `y⋆ = [y⋆ + δ 𝓕(X⋆)]_+` (eq. (4.3)), the positive part taken entrywise. -/
theorem optimal_dual_fixed_point {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ i : Fin m, ys i = max (ys i + δ * constraintMap f Xs i) 0 := by sorry

end CaiCandesShen.GeneralConvex
