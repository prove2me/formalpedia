-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_staticValue_attained
-- name    : BudgetedAffine.Budget.staticValue_attained
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:31.861935+00:00
-- url     : https://prove2.me/theorems/4794f263-af9b-4f70-9d5e-7095c405898f
-- title:
--   The static problem (3.4)/(4.6) attains its minimum when feasible
-- statement:
--   Let $A,B\in\mathbb R^{m\times n}$, $c,d\in\mathbb R^n$ with $d\ge0$, and let $\mathcal X$ be a polyhedron with $c^\top x\ge0$ for every $x\in\mathcal X$. For a right-hand side $r\in\mathbb R^m$, consider the static problem
--   $$z_{Sta}(r)=\min_{x\in\mathcal X,\ y\ge0}\{c^\top x+d^\top y : Ax+By\ge r\}.$$
--   If it is feasible, i.e. $z_{Sta}(r)<+\infty$, then the minimum is attained: there are $x_{Sta}\in\mathcal X$ and $y_{Sta}\ge0$ with $Ax_{Sta}+By_{Sta}\ge r$ and $c^\top x_{Sta}+d^\top y_{Sta}=z_{Sta}(r)$.
--
--   The paper takes such an arg min $(x_{Sta},y_{Sta})$ as the static part of the affine policies (3.5) and (4.7).
--
--   **Formalization Note** $z_{Sta}$ is the $\mathrm{EReal}$-valued infimum `staticValue`, and optimality is `IsStaticOpt` (definition `BudgetedAffine_Budget_Construction`). The objective is bounded below by $0$ on the feasible set, so attainment is the standard linear-programming fact.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, static problem (3.4), p. 8, and (4.6), p. 18 ('(x_Sta, y_Sta) ∈ arg min'); LP attainment: Bertsimas–Tsitsiklis, Introduction to Linear Optimization, Corollary 2.3, p. 67

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

namespace BudgetedAffine.Budget

open Matrix

/-- The static problem (3.4)/(4.6), `min_{x ∈ X, y ≥ 0} {cᵀx + dᵀy | A x + B y ≥ r}` over a
polyhedron `X` with `cᵀx ≥ 0` on `X` and `d ≥ 0`, attains its minimum whenever it is feasible
(value `≠ +∞`). -/
theorem staticValue_attained {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (r : Fin m → ℝ) (hX : IsPolyhedral X) (hd : 0 ≤ d)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hfin : staticValue A B c d X r ≠ ⊤) :
    ∃ x y : Fin n → ℝ, IsStaticOpt A B c d X r x y := by sorry

end BudgetedAffine.Budget
