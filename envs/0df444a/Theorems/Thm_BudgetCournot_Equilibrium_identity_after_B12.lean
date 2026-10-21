-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_identity_after_B12
-- name    : BudgetCournot.Equilibrium.identity_after_B12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:59.25011+00:00
-- url     : https://prove2.me/theorems/3c9ee44b-dc52-4e77-b4bb-641cc7d9079e
-- title:
--   Identity after (B-12), p. 19 — Σ_{k≤n} λ_k/(1+n) = Σ_{k≤n} α_k/(k(k+1))
-- statement:
--   Let $\lambda_1,\dots,\lambda_N$ and $\alpha_1,\dots,\alpha_N$ satisfy $\alpha_i=i\,\lambda_i-\sum_{k=1}^{i-1}\lambda_k$ for every $i$, as in (B-10). Then for every $n\in\{0,1,\dots,N\}$,
--
--   $$\sum_{k=1}^{n}\frac{\lambda_k}{1+n}=\sum_{k=1}^{n}\frac{\alpha_k}{k(k+1)}.$$
--
--   With $n=n_j$, this turns the multiplier form (B-7) of the equilibrium allocations into the level form (B-12).
--
--   **Formalization Note** The middle expression of the printed chain, $\frac1{1+n}\sum_{k}(\alpha_k/k+\sum_{l<k}\alpha_l/(l(l+1)))$, is (B-11) substituted and is not stated separately.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 19, proof of Theorem 1, identity after (B-12)

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- Identity after (B-12), p. 19: under (B-10), for every `n ≤ N`,
`∑_{k=1}^{n} λ_k / (1+n) = ∑_{k=1}^{n} α_k / (k(k+1))`. -/
theorem identity_after_B12 {N : ℕ} (lam α : Fin N → ℝ)
    (h : ∀ i, α i = ((i : ℕ) + 1 : ℝ) * lam i - ∑ k ∈ univ.filter (fun k => k < i), lam k)
    (n : ℕ) (hn : n ≤ N) :
    (∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n), lam k) / (1 + (n : ℝ)) =
      ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
        α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) := by sorry

end BudgetCournot.Equilibrium
