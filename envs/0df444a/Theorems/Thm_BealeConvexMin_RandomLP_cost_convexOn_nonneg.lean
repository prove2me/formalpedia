-- Prove2me | Theorems.Thm_BealeConvexMin_RandomLP_cost_convexOn_nonneg
-- name    : BealeConvexMin.RandomLP.cost_convexOn_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:42:05.818608+00:00
-- url     : https://prove2.me/theorems/2ac012f7-34eb-40ae-a196-ce5f0dc5dcb1
-- title:
--   Beale (1955), proof of Theorem 2: for fixed A and β, C(x) is convex on x ≥ 0
-- statement:
--   Fix the data $A\in\mathbb R^{m\times n}$ and $\beta\in\mathbb R^m$, together with the constants $c\in\mathbb R^n$, $f\in\mathbb R^p$, $D\in\mathbb R^{m\times p}$. For $x\in\mathbb R^n$ let
--   $$C(x)=c'x+\min\{f'y : y\ge 0,\ Ax+Dy=\beta\}.$$
--   Assume that for every non-negative $x$ this minimum over $y$ is attained. Then for all non-negative $x_1,x_2$ and all $\lambda_1,\lambda_2\ge0$ with $\lambda_1+\lambda_2=1$,
--   $$C(\lambda_1x_1+\lambda_2x_2)\le\lambda_1C(x_1)+\lambda_2C(x_2),$$
--   that is, $C$ is a convex function on the non-negative orthant.
--
--   This is the pointwise inequality, "for any fixed values of $A$ and $\beta$", from which Beale obtains Theorem 2 by integrating over the distribution of the data.
--
--   **Formalization Note** The attainment hypothesis is the paper's implicit premise that the minimising $y(x)$ exists; without it the real infimum would be a junk $0$ where the second stage is infeasible or unbounded.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 182 (PDF p. 10), proof of Theorem 2, last display

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
import Definitions.Def_BealeConvexMin_RandomLP_expectedCost

namespace BealeConvexMin.RandomLP

open Matrix

/-- Beale (1955), §5, p. 182, proof of Theorem 2, last display: for fixed values of `A` and `β`,
`C(λ₁x₁ + λ₂x₂) ≤ λ₁C(x₁) + λ₂C(x₂)` for all non-negative `x₁`, `x₂` and `λ₁, λ₂ ≥ 0` with
`λ₁ + λ₂ = 1`, where `C(x)` is the minimum over `y` of (5.3) subject to (5.4). The second-stage
minimum is assumed attained at every non-negative `x` (the paper's `y(x)`). -/
theorem cost_convexOn_nonneg {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ)
    (hatt : ∀ x : Fin n → ℝ, 0 ≤ x → SecondStageAttained D f (β - A *ᵥ x)) :
    ConvexOn ℝ {x : Fin n → ℝ | 0 ≤ x} (cost c f D A β) := by sorry

end BealeConvexMin.RandomLP
