-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_theorem_1
-- name    : BudgetCournot.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:59.47+00:00
-- url     : https://prove2.me/theorems/9eadac99-dee9-4382-aa0d-553d6ae8d6c7
-- title:
--   Theorem 1, p. 8 — the unique Cournot equilibrium is x*_ij of (6), in augmented budgets 𝓑_i, cutoff budgets 𝔹_j and H
-- statement:
--   Consider $N$ budget-constrained firms competing in $M$ linear markets $r_j(X)=R_j-X/\beta_j$, with $0\le R_1\le\cdots\le R_M$, $\beta_j>0$, and budgets $B_1\ge\cdots\ge B_N>0$. Let $\mathcal B_i=iB_i+\sum_{k=i}^NB_k$ be the augmented budgets (4), $\mathbb B_j=\sum_{k=j}^M\beta_k(R_k-R_j)$ the cutoff budgets (5), $H$ the function of Definition 3.2, and $n^*_j=\max\{i\in[N]:\mathcal B_i>\mathbb B_j\}$ (zero if no firm qualifies), equation (7).
--
--   Then there is a unique Cournot equilibrium, and it is
--
--   $$x^*_{ij}=\beta_j\Big[\frac{R_j}{1+n^*_j}-\frac{H(\mathcal B_i)}{i+1}+\sum_{k=1}^{n^*_j}\frac{H(\mathcal B_k)}{k(k+1)}-\sum_{k=1}^{i}\frac{H(\mathcal B_k)}{k(k+1)}\Big]^+.\qquad(6)$$
--
--   Equivalently: an allocation profile is a Cournot equilibrium if and only if it equals $x^*$. The closed form shows that firm $i$'s allocation depends on the budgets only through $\mathcal B_i,\dots,\mathcal B_N$.
--
--   **Formalization Note** The statement is the equivalence `IsCournotEq R β B x ↔ x = xStar R β B` for every profile $x$, which contains existence, uniqueness and the closed form. `xStar` is the explicit formula (6). The orderings of §2, made "without loss of generality", are hypotheses; budgets may tie. Paper firm $i$ is Lean index $i.\mathrm{val}+1$. The page calls $n^*_j$ the number of active firms, but at $R_j=0$ the threshold index may be positive while every allocation to market $j$ is zero; the Lean conclusion does not assert that false boundary interpretation.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 8, Theorem 1

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- Theorem 1, p. 8: under the standing assumptions, a profile is a Cournot equilibrium iff it
equals the closed form (6); so the equilibrium exists, is unique, and is given by (6). -/
theorem theorem_1 {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) :
    IsCournotEq R β B x ↔ x = xStar R β B := by sorry

end BudgetCournot.Equilibrium
