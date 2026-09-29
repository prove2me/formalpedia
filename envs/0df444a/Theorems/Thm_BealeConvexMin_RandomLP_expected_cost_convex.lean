-- Prove2me | Theorems.Thm_BealeConvexMin_RandomLP_expected_cost_convex
-- name    : BealeConvexMin.RandomLP.expected_cost_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:43:57.286059+00:00
-- url     : https://prove2.me/theorems/86c44daa-2826-4c9c-9cc8-d72627996aa6
-- title:
--   Beale (1955), Theorem 2: E(C) is a convex function of x
-- statement:
--   Let $(\Omega,P)$ be a probability space carrying the random data: an $m\times n$ matrix $A(\omega)=(\alpha_{ij}(\omega))$ and a vector $\beta(\omega)\in\mathbb R^m$. Let $c\in\mathbb R^n$, $f\in\mathbb R^p$ and $D\in\mathbb R^{m\times p}$ be constants. For a first-stage vector $x\ge0$ and an outcome $\omega$, the cost is
--   $$C(x,\omega)=c'x+\min\{f'y : y\ge 0,\ A(\omega)x+Dy=\beta(\omega)\},$$
--   and its mean value is $E(C)(x)=\int_\Omega C(x,\omega)\,dP(\omega)$.
--
--   Assume that for every $x\ge0$:
--
--   1. for $P$-almost every $\omega$ the minimum over $y$ defining $C(x,\omega)$ is attained;
--   2. $\omega\mapsto C(x,\omega)$ is integrable, so that the mean value $E(C)(x)$ exists.
--
--   Then $E(C)$ is a convex function of $x$ on the non-negative orthant: for $x_1,x_2\ge0$ and $\lambda_1,\lambda_2\ge0$ with $\lambda_1+\lambda_2=1$,
--   $$E(C)(\lambda_1x_1+\lambda_2x_2)\le\lambda_1E(C)(x_1)+\lambda_2E(C)(x_2).$$
--
--   This is Theorem 2 of the paper. It makes the first-stage problem of a two-stage linear program with random coefficients a convex minimisation over $x\ge0$, for any known distribution of the data.
--
--   **Formalization Note** The paper uses both hypotheses without stating them: it speaks of "the value of $y$ that minimizes $C$" and of "the mean value $E(C)$". Without them the real infimum and the Bochner integral would return junk zeros. Attainment is required only almost surely, which is weaker than "for all fixed values of $A$ and $\beta$" and so gives a slightly stronger theorem. No moment, complete-recourse or finite-support assumption is made.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 182 (PDF p. 10), Theorem 2

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
import Definitions.Def_BealeConvexMin_RandomLP_expectedCost

namespace BealeConvexMin.RandomLP

open Matrix MeasureTheory

/-- Beale (1955), §5, p. 182, Theorem 2: `E(C)` is a convex function of `x` on the non-negative
orthant. The data `A`, `β` are random on a probability space `(Ω, P)`; `c`, `f`, `D` are constant.
Assumed, as the paper does implicitly: for each non-negative `x`, the second-stage minimum is
attained for almost every realisation of `(A, β)`, and `C(x, ·)` is integrable (so that the mean
value `E(C)` exists). -/
theorem expected_cost_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (A : Ω → Matrix (Fin m) (Fin n) ℝ) (β : Ω → Fin m → ℝ)
    (hatt : ∀ x : Fin n → ℝ, 0 ≤ x → ∀ᵐ ω ∂P, SecondStageAttained D f (β ω - A ω *ᵥ x))
    (hint : ∀ x : Fin n → ℝ, 0 ≤ x → Integrable (fun ω => cost c f D (A ω) (β ω) x) P) :
    ConvexOn ℝ {x : Fin n → ℝ | 0 ≤ x} (expectedCost P c f D A β) := by sorry

end BealeConvexMin.RandomLP
