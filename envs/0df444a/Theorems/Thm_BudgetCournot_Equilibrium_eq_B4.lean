-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_eq_B4
-- name    : BudgetCournot.Equilibrium.eq_B4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:07.020981+00:00
-- url     : https://prove2.me/theorems/09431cad-19ca-44f9-8dfa-4e2d207023eb
-- title:
--   (B-4), p. 18 — a firm's best response is water-filling with a budget multiplier λ_i ≥ 0
-- statement:
--   Assume the standing assumptions of the model. Fix a profile $x$ and a firm $i$, and let $X_{ij-}=\sum_{k\ne i}x_{kj}$ be the others' total in market $j$. Firm $i$'s allocation is feasible and solves its problem (2) against $X_{i-}$ — no feasible allocation $y$ gives firm $i$ a higher profit when the others keep their allocations — if and only if there is $\lambda_i\ge 0$ with
--
--   $$x_{ij}=\frac{(\beta_jR_j-\beta_j\lambda_i-X_{ij-})^+}{2}\quad\text{for all }j,$$
--
--   $\sum_j x_{ij}\le B_i$, and $\lambda_i=0$ or $\sum_j x_{ij}=B_i$.
--
--   This is the first step of the proof of Theorem 1: it reduces each firm's optimization to a one-dimensional choice of the multiplier.
--
--   **Formalization Note** "$\lambda_i$ is the smallest real such that $\sum_j x_{ij}\le B_i$" is encoded as complementary slackness; since $B_i>0$ the two readings determine the same $\lambda_i$. The others' allocations are arbitrary reals; no sign condition is placed on them.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 18, proof of Theorem 1, (B-4)

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- (B-4), p. 18: firm `i`'s allocation solves (2) against the others' allocations iff it is
the water-filling response `x_ij = (β_j R_j - β_j λ_i - X_{ij-})⁺/2` for a multiplier `λ_i ≥ 0`
with the budget constraint and complementary slackness. -/
theorem eq_B4 {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) (i : Fin N) :
    (x i ∈ feasible B i ∧
        ∀ y ∈ feasible B i, payoff R β i (Function.update x i y) ≤ payoff R β i x) ↔
      ∃ lam : ℝ, IsBR R β B i x lam := by sorry

end BudgetCournot.Equilibrium
