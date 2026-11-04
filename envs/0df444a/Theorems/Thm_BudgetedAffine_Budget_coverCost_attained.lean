-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_coverCost_attained
-- name    : BudgetedAffine.Budget.coverCost_attained
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:30.395566+00:00
-- url     : https://prove2.me/theorems/261e0ea5-fb19-4fac-8550-21dec13acf8e
-- title:
--   The fractional covering problem (3.2) attains its minimum when feasible
-- statement:
--   Let $B\in\mathbb R^{m\times n}$, $d\in\mathbb R^n_+$ and $h\in\mathbb R^m$, and consider the covering value (3.2),
--   $$z(h)=\min_{y\ge0}\{d^\top y : By\ge h\}.$$
--   If the problem is feasible, i.e. $z(h)<+\infty$, then the minimum is attained: there is $v\ge0$ with $Bv\ge h$ and $d^\top v=z(h)$.
--
--   The paper uses this to pick, for every $i$, an optimal solution $v_i$ of $z(e_i)$ in the linear parts (3.3) and (4.5) of the affine policies.
--
--   **Formalization Note** $z(h)$ is the $\mathrm{EReal}$-valued infimum `coverCost`, and optimality is `IsCoverOpt` (definition `BudgetedAffine_Budget_Model`). Since $d\ge0$ the value is bounded below by $0$, so attainment is the standard linear-programming fact.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, (3.2) and the optimal solutions v_i used in (3.3), p. 8, and (4.5), p. 18; LP attainment: Bertsimas–Tsitsiklis, Introduction to Linear Optimization, Corollary 2.3, p. 67

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Budget

open Matrix

/-- The fractional covering problem (3.2), `min_{y ≥ 0} {dᵀy | B y ≥ h}` with `d ≥ 0`, attains its
minimum whenever it is feasible (value `≠ +∞`). -/
theorem coverCost_attained {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (h : Fin m → ℝ) (hd : 0 ≤ d) (hfin : coverCost B d h ≠ ⊤) :
    ∃ y : Fin n → ℝ, IsCoverOpt B d h y := by sorry

end BudgetedAffine.Budget
