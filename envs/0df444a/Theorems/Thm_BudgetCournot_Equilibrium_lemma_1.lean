-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_lemma_1
-- name    : BudgetCournot.Equilibrium.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:02.346962+00:00
-- url     : https://prove2.me/theorems/698f7f3b-5a7a-4e00-a06f-68b40ab1c4ac
-- title:
--   Lemma 1, p. 20 — (i+1)Σ_j V_j x_ij + Σ_{k>i}Σ_j V_j x_kj = Σ_{j: α_i<R_j} V_j β_j (R_j − α_i) for the allocations (B-12)
-- statement:
--   Let $R_1,\dots,R_M\ge 0$ and $\beta_1,\dots,\beta_M>0$, and let $0\le\alpha_1\le\alpha_2\le\cdots\le\alpha_N$. Put $n_j=\max\{i\in\{0\}\cup[N]:\alpha_i\le R_j\}$ as in (B-13) and
--
--   $$x_{ij}=\beta_j\Big[\frac{R_j}{1+n_j}-\frac{\alpha_i}{i+1}+\sum_{k=1}^{n_j}\frac{\alpha_k}{k(k+1)}-\sum_{k=1}^{i}\frac{\alpha_k}{k(k+1)}\Big]^+$$
--
--   as in (B-12). Then for every vector $(V_1,\dots,V_M)$ and every firm $i$,
--
--   $$(i+1)\sum_{j=1}^M V_jx_{ij}+\sum_{k=i+1}^N\sum_{j=1}^M V_jx_{kj}=\sum_{j:\,\alpha_i<R_j}V_j\beta_j(R_j-\alpha_i).$$
--
--   With $V\equiv 1$ this converts the budget constraints of the firms into the inequalities (B-16) on the levels $\alpha_i$.
--
--   **Formalization Note** The lemma is an identity about the allocations (B-12) built from any non-decreasing $\alpha\ge 0$; no equilibrium is assumed. The market ordering $R_1\le\cdots\le R_M$ is not assumed: both sides split market by market, and $x_{ij}$ depends on market $j$ only through $R_j,\beta_j$, so the statement holds for markets in any order (a strengthening of the page, confirmed numerically). The empty maximum in (B-13) is $0$.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 20, Lemma 1, (B-18); (B-12), (B-13), p. 19

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- Lemma 1 (B-18), p. 20: for non-decreasing levels `α ≥ 0`, the allocations `x_ij` of (B-12)
with `n_j` of (B-13) satisfy, for every vector `V` and paper index `i`,
`(i+1) ∑_j V_j x_ij + ∑_{k>i} ∑_j V_j x_kj = ∑_{j : α_i < R_j} V_j β_j (R_j - α_i)`. -/
theorem lemma_1 {N M : ℕ} (R β : Fin M → ℝ) (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j)
    (α : Fin N → ℝ) (hα : Monotone α) (hα0 : ∀ i, 0 ≤ α i) (V : Fin M → ℝ) (i : Fin N) :
    ((i : ℕ) + 2 : ℝ) * ∑ j, V j * xAlpha R β α i j
        + ∑ k ∈ univ.filter (fun k => i < k), ∑ j, V j * xAlpha R β α k j =
      ∑ j ∈ univ.filter (fun j => α i < R j), V j * β j * (R j - α i) := by sorry

end BudgetCournot.Equilibrium
