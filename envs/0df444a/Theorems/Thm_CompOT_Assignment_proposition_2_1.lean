-- Prove2me | Theorems.Thm_CompOT_Assignment_proposition_2_1
-- name    : CompOT.Assignment.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:20.162477+00:00
-- url     : https://prove2.me/theorems/61c2f0a6-8e84-4079-bd9f-062eb4a8c1d4
-- title:
--   Proposition 2.1, pp. 372–373 — a permutation coupling optimizes the uniform Kantorovich problem
-- statement:
--   Let $n>0$, let $C$ be any real $n\times n$ cost matrix, and let $u$ be the histogram with entries $1/n$. There is a permutation $\sigma^\star$ such that its scaled permutation coupling is optimal among **all** couplings in $U(u,u)$, and $\sigma^\star$ minimizes the assignment objective among all permutations:
--
--   $$P_{\sigma^\star}\in U(u,u),\qquad \langle C,P_{\sigma^\star}\rangle\le\langle C,Q\rangle\quad(\forall Q\in U(u,u)),\qquad A_C(\sigma^\star)\le A_C(\tau)\quad(\forall\tau\in\operatorname{Perm}(n)).$$
--
--   Consequently, the Kantorovich relaxation of the uniform optimal assignment problem is tight.
--
--   **Formalization Note** The condition $n>0$ excludes the empty index set and division by zero. The cost is allowed to be negative; the book imposes no sign restriction on $C$ for this result. The minimization over couplings ranges over every feasible matrix, not only permutation matrices.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 2.1, pp. 372–373

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem proposition_2_1 {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ∃ σ : Equiv.Perm (Fin n),
      IsOptimalCoupling C (uniform n) (uniform n) (permCoupling σ) ∧
      ∀ τ : Equiv.Perm (Fin n), assignmentCost C σ ≤ assignmentCost C τ := by sorry

end CompOT.Assignment
