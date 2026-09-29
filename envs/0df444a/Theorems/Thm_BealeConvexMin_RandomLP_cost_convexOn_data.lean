-- Prove2me | Theorems.Thm_BealeConvexMin_RandomLP_cost_convexOn_data
-- name    : BealeConvexMin.RandomLP.cost_convexOn_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:42:33.687886+00:00
-- url     : https://prove2.me/theorems/ef5aef7b-69e2-4e1e-9377-8a646ca962b8
-- title:
--   Beale (1955), Theorem 3: given x, C is a convex function of (A, β)
-- statement:
--   Fix constants $c\in\mathbb R^n$, $f\in\mathbb R^p$, $D\in\mathbb R^{m\times p}$ and a non-negative first-stage vector $x\in\mathbb R^n$, $x\ge 0$. For data $(A,\beta)\in\mathbb R^{m\times n}\times\mathbb R^m$ let
--   $$C(A,\beta)=c'x+\min\{f'y : y\ge 0,\ Ax+Dy=\beta\}.$$
--   Let $K$ be a convex set of data pairs $(A,\beta)$ such that for every $(A,\beta)\in K$ the minimum over $y$ is attained. Then $C$ is jointly convex on $K$: for $(A_1,\beta_1),(A_2,\beta_2)\in K$ and $\lambda_1,\lambda_2\ge0$ with $\lambda_1+\lambda_2=1$,
--   $$C(\lambda_1A_1+\lambda_2A_2,\ \lambda_1\beta_1+\lambda_2\beta_2)\le\lambda_1C(A_1,\beta_1)+\lambda_2C(A_2,\beta_2).$$
--
--   This is Theorem 3 of the paper, "Given $x$, $C$ is a convex function of $A$ and $\beta$". Beale uses it to argue that adding a zero-mean random perturbation to the coefficients cannot decrease $E(C)$.
--
--   **Formalization Note** The paper names no domain for $(A,\beta)$. The statement is made on every convex set of data on which the second-stage minimum is attained, i.e. every convex set on which $C$ is defined as a minimum; attainment is needed because the real infimum is a junk $0$ elsewhere. The first-stage vector $x$ is taken non-negative, as in the paper's model ("choose non-negative $x_j$", p. 181); the page says only "given $x$".
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 182 (PDF p. 10), Theorem 3

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
import Definitions.Def_BealeConvexMin_RandomLP_expectedCost

namespace BealeConvexMin.RandomLP

open Matrix

/-- Beale (1955), §5, p. 182, Theorem 3: given `x`, `C` is a convex function of `A` and `β`
jointly. For a non-negative first-stage `x` (the model's "choose non-negative x_j", p. 181) and
every convex set `K` of data pairs `(A, β)` on which the second-stage minimum is
attained, `(A, β) ↦ C = c′x + min {f′y | y ≥ 0, Ax + Dy = β}` is convex on `K`. -/
theorem cost_convexOn_data {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (K : Set (Matrix (Fin m) (Fin n) ℝ × (Fin m → ℝ))) (hK : Convex ℝ K)
    (hatt : ∀ q ∈ K, SecondStageAttained D f (q.2 - q.1 *ᵥ x)) :
    ConvexOn ℝ K (fun q => cost c f D q.1 q.2 x) := by sorry

end BealeConvexMin.RandomLP
