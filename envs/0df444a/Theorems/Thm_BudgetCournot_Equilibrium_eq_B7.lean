-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_eq_B7
-- name    : BudgetCournot.Equilibrium.eq_B7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:58.832155+00:00
-- url     : https://prove2.me/theorems/2592cda9-4342-42f2-830b-04788b1b71c4
-- title:
--   (B-5)–(B-7), p. 18 — in equilibrium λ_1 ≤ ⋯ ≤ λ_N, the active firms are the first n_j, and x_ij has the λ-closed form
-- statement:
--   Assume the standing assumptions. Let $x$ be a Cournot equilibrium and let $\lambda_1,\dots,\lambda_N$ be multipliers for which each firm satisfies the best-response condition (B-4). For each market $j$ let $n_j$ be the number of firms with $x_{ij}>0$. Then
--
--   1. $\lambda_1\le\lambda_2\le\cdots\le\lambda_N$;
--   2. $x_{ij}=0$ for every firm $i>n_j$;
--   3. for every $i$ and $j$,
--   $$x_{ij}=\frac{\beta_j}{n_j+1}\Big[R_j-\lambda_i(n_j+1)+\sum_{k=1}^{n_j}\lambda_k\Big]^+ .$$
--
--   This expresses the equilibrium in terms of the multipliers alone, market by market.
--
--   **Formalization Note** The multipliers are tied to $x$ by the best-response predicate of the model file (water-filling formula, budget constraint, complementary slackness); they are not free parameters. Paper firm $i$ is Lean index $i.\mathrm{val}+1$, so "$i>n_j$" is `n_j ≤ i.val`.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 18, proof of Theorem 1, (B-5)–(B-7)

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- (B-5)–(B-7), p. 18: at a Cournot equilibrium with budget multipliers `λ_i`, the multipliers
are non-decreasing in `i`, in each market only the first `n_j` firms are active, and
`x_ij = β_j/(n_j+1) [R_j - λ_i (n_j+1) + ∑_{k=1}^{n_j} λ_k]⁺`. -/
theorem eq_B7 {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) (lam : Fin N → ℝ) (hx : IsCournotEq R β B x)
    (hlam : ∀ i, IsBR R β B i x (lam i)) :
    Monotone lam ∧
      ∀ j, (∀ i : Fin N, nActive x j ≤ (i : ℕ) → x i j = 0) ∧
        ∀ i, x i j = β j / ((nActive x j : ℝ) + 1) *
          max 0 (R j - lam i * ((nActive x j : ℝ) + 1)
            + ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < nActive x j), lam k) := by sorry

end BudgetCournot.Equilibrium
