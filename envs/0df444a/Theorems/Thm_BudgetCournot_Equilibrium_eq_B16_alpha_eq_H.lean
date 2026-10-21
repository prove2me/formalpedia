-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_eq_B16_alpha_eq_H
-- name    : BudgetCournot.Equilibrium.eq_B16_alpha_eq_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:02.255061+00:00
-- url     : https://prove2.me/theorems/bebf2cc1-3f8d-4585-b50a-f33d02af4f9d
-- title:
--   (B-16) and end of the proof of Theorem 1, p. 20 — in equilibrium α_i = H(𝓑_i)
-- statement:
--   Assume the standing assumptions. Let $x$ be a Cournot equilibrium and $\lambda_1,\dots,\lambda_N$ multipliers for which each firm satisfies the best-response condition (B-4), and set $\alpha_i=i\lambda_i-\sum_{k=1}^{i-1}\lambda_k$ as in (B-10). Then for every firm $i$,
--
--   $$\sum_{j:\,\alpha_i<R_j}\beta_j(R_j-\alpha_i)\le(i+1)B_i+\sum_{l=i+1}^N B_l=\mathcal B_i\qquad\text{and}\qquad \alpha_i=H(\mathcal B_i).$$
--
--   Together with (B-11) and Lemma 1 this pins down the multipliers, and hence the equilibrium, in terms of the augmented budgets.
--
--   **Formalization Note** The multipliers are tied to $x$ by the best-response predicate (water-filling formula, budget constraint, complementary slackness). Paper firm $i$ is Lean index $i.\mathrm{val}+1$.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 20, proof of Theorem 1, (B-16) and the last paragraph

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- (B-16) and the end of the proof of Theorem 1, p. 20: at a Cournot equilibrium with budget
multipliers `λ_i`, the levels `α_i = i λ_i - ∑_{k=1}^{i-1} λ_k` of (B-10) satisfy
`∑_{j : α_i < R_j} β_j (R_j - α_i) ≤ 𝓑_i` and `α_i = H(𝓑_i)`. -/
theorem eq_B16_alpha_eq_H {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) (lam : Fin N → ℝ) (hx : IsCournotEq R β B x)
    (hlam : ∀ i, IsBR R β B i x (lam i)) (i : Fin N) :
    let α : Fin N → ℝ := fun i =>
      ((i : ℕ) + 1 : ℝ) * lam i - ∑ k ∈ univ.filter (fun k => k < i), lam k
    (∑ j ∈ univ.filter (fun j => α i < R j), β j * (R j - α i) ≤ augBudget B i) ∧
      α i = H R β (augBudget B i) := by sorry

end BudgetCournot.Equilibrium
