-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_eq_B11
-- name    : BudgetCournot.Equilibrium.eq_B11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:53.401714+00:00
-- url     : https://prove2.me/theorems/d6802b42-264c-4ea0-a499-67070b9f751b
-- title:
--   (B-10) ⇒ (B-11), p. 19 — λ_i = α_i/i + Σ_{k<i} α_k/(k(k+1))
-- statement:
--   Let $\lambda_1,\dots,\lambda_N$ and $\alpha_1,\dots,\alpha_N$ be real numbers with
--
--   $$\alpha_i=i\,\lambda_i-\sum_{k=1}^{i-1}\lambda_k\qquad(i=1,\dots,N).$$
--
--   Then for every $i$,
--
--   $$\lambda_i=\frac{\alpha_i}{i}+\sum_{k=1}^{i-1}\frac{\alpha_k}{k(k+1)}.$$
--
--   The proof of Theorem 1 replaces the multipliers $\lambda_i$ by the levels $\alpha_i$; this identity inverts that change of variables.
--
--   **Formalization Note** Indices are 0-based in Lean: paper index $k$ is `k.val + 1`, so $k(k+1)$ is `(k+1)(k+2)`. No sign or order conditions are needed.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 19, proof of Theorem 1, (B-10), (B-11)

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- (B-10) ⇒ (B-11), p. 19: if `α_i = i λ_i - ∑_{k=1}^{i-1} λ_k` for every `i`, then
`λ_i = α_i / i + ∑_{k=1}^{i-1} α_k / (k(k+1))` (paper indices; `Fin` index `k` is paper `k+1`). -/
theorem eq_B11 {N : ℕ} (lam α : Fin N → ℝ)
    (h : ∀ i, α i = ((i : ℕ) + 1 : ℝ) * lam i - ∑ k ∈ univ.filter (fun k => k < i), lam k)
    (i : Fin N) :
    lam i = α i / ((i : ℕ) + 1 : ℝ)
      + ∑ k ∈ univ.filter (fun k => k < i), α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) := by sorry

end BudgetCournot.Equilibrium
