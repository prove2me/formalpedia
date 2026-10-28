-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_H_least_feasible_B17
-- name    : BudgetCournot.Equilibrium.H_least_feasible_B17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:56.974008+00:00
-- url     : https://prove2.me/theorems/29e0fdb7-5598-4c5e-908d-3810e0ec254f
-- title:
--   Proof of Theorem 1, p. 20, after (B-17) — H(x) is the least z ≥ 0 meeting the budget inequality, which binds when H(x) > 0
-- statement:
--   Let $0\le R_1\le\cdots\le R_M$, $\beta_1,\dots,\beta_M>0$, and $x\ge 0$, and let $H$ be the function of Definition 3.2. Then $H(x)\ge 0$,
--
--   $$\sum_{j=1}^M\beta_j\big(R_j-H(x)\big)^+\le x,$$
--
--   every $z\ge 0$ with $\sum_j\beta_j(R_j-z)^+\le x$ satisfies $H(x)\le z$, and either $H(x)=0$ or the inequality above is an equality.
--
--   In words, $H(x)$ is the smallest nonnegative level satisfying the budget inequality, and when it is positive it makes the inequality tight. This is what the proof of Theorem 1 uses to identify the level $\alpha_i$ of firm $i$ with $H(\mathcal B_i)$ from (B-16) and (B-17); note $\sum_j\beta_j(R_j-\alpha)^+=\sum_{j:\alpha<R_j}\beta_j(R_j-\alpha)$.
--
--   **Formalization Note** The page's "greater than one" is read as "greater than zero" (a printed slip). Only the market part of the standing assumptions is assumed.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 20, proof of Theorem 1, paragraph after (B-17)

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- Proof of Theorem 1, p. 20, after (B-17): for `x ≥ 0`, `H(x)` is the smallest `z ≥ 0` with
`∑_j β_j (R_j - z)⁺ ≤ x`, it satisfies that inequality, and the inequality is an equality
whenever `H(x) > 0`. -/
theorem H_least_feasible_B17 {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R)
    (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ H R β x ∧ ∑ j, β j * max (R j - H R β x) 0 ≤ x ∧
      (∀ z : ℝ, 0 ≤ z → ∑ j, β j * max (R j - z) 0 ≤ x → H R β x ≤ z) ∧
      (H R β x = 0 ∨ ∑ j, β j * max (R j - H R β x) 0 = x) := by sorry

end BudgetCournot.Equilibrium
