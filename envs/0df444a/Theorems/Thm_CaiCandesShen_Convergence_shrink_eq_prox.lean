-- Prove2me | Theorems.Thm_CaiCandesShen_Convergence_shrink_eq_prox
-- name    : CaiCandesShen.Convergence.shrink_eq_prox
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:14:14.707207+00:00
-- url     : https://prove2.me/theorems/d434d624-8e91-4917-bfa9-8cf1ff10ee40
-- title:
--   Theorem 2.1 — $\mathcal D_\tau(Y)=\arg\min_X \tfrac12\|X-Y\|_F^2+\tau\|X\|_*$
-- statement:
--   Let $\tau\ge0$ and $Y\in\mathbb R^{n_1\times n_2}$. The singular value shrinkage operator is the proximity operator of $\tau\|\cdot\|_*$:
--   $$\mathcal D_\tau(Y)=\arg\min_X\ \tfrac12\|X-Y\|_F^2+\tau\|X\|_*.$$
--   That is, if $X=\mathcal D_\tau(Y)$ then (i) $X$ minimizes $h(Z)=\tfrac12\|Z-Y\|_F^2+\tau\|Z\|_*$ over all $Z$, and (ii) every minimizer of $h$ equals $X$.
--
--   This is what makes each step of the SVT iteration an exact minimization of a Lagrangian, and identifies the algorithm with Uzawa's method.
--
--   **Formalization Note** "$\arg\min$" is read as "the unique minimizer", and both minimality and uniqueness are stated. The hypothesis is $\tau\ge0$, as printed (not the standing $\tau>0$ of later sections).
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1960, Theorem 2.1, Eq. (2.3)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Shrink

namespace CaiCandesShen.Convergence

/-- Theorem 2.1, p. 1960: for `τ ≥ 0`, `D_τ(Y)` is the unique minimizer of
`½‖X - Y‖_F² + τ‖X‖_*`. -/
theorem shrink_eq_prox {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (Y X : Mat n₁ n₂)
    (hX : IsShrink τ Y X) :
    (∀ X' : Mat n₁ n₂,
        1 / 2 * frobNorm (X - Y) ^ 2 + τ * nuclearNorm X ≤
          1 / 2 * frobNorm (X' - Y) ^ 2 + τ * nuclearNorm X') ∧
    (∀ X' : Mat n₁ n₂,
        (∀ X'' : Mat n₁ n₂,
          1 / 2 * frobNorm (X' - Y) ^ 2 + τ * nuclearNorm X' ≤
            1 / 2 * frobNorm (X'' - Y) ^ 2 + τ * nuclearNorm X'') → X' = X) := by sorry

end CaiCandesShen.Convergence
