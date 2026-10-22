-- Prove2me | Theorems.Thm_BudgetedPCTSP_Rooted_optimal_le_potential_bound
-- name    : BudgetedPCTSP.Rooted.optimal_le_potential_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T14:32:38.508227+00:00
-- url     : https://prove2.me/theorems/9259dd3a-a316-4651-9622-9dc1a5b17a89
-- title:
--   Theorem 1 — every feasible tour visits at most λ₁D + π(O) vertices
-- statement:
--   Fix an instance $(G, c, D, r)$ of the rooted budgeted prize-collecting traveling salesman problem and a value $\lambda_1 \ge 0$.
--
--   (i) The primal-dual subroutine PD($\lambda_1$) has a complete run.
--
--   (ii) Let $y$ and $\mathcal S$ come from any complete run of PD($\lambda_1$), under any order of breaking ties, with potentials $\pi(S) = |S| - 2\sum_{T \subsetneq S} y_T$, and let $\mathcal S^+ = \mathcal S \cup \{V\}$. Let $O^\star$ be the set of vertices visited by a feasible tour (a closed walk at $r$ of cost at most $D$), and let $O$ be a minimal set of $\mathcal S^+$ containing $O^\star$. Then
--   $$|O^\star| \le \lambda_1 D + \pi(O) .$$
--
--   This is the dual-fitting upper bound of the paper: applied to an optimal tour, it bounds the optimum by a quantity computed from the subroutine's output. Combined with the lower bound $|S_A| > \tfrac12 \lambda_1 D + \pi(Q) - 1$ on the algorithm's tour (Theorem 2), it yields the paper's 2-approximation (Theorem 3).
--
--   **Formalization Note.** The paper takes $O^\star$ from an optimal tour; its proof uses only that the tour is feasible, so the statement is made for every feasible tour, which contains the optimal case. "The minimal set in $\mathcal S^+$ that contains $O^\star$" is read as any set of $\mathcal S^+$ containing $O^\star$ with no strict subset in $\mathcal S^+$ containing $O^\star$; one exists because $V \in \mathcal S^+$, and it is unique because $\mathcal S^+$ is laminar. Part (i) is the formal counterpart of "assume that we have run the primal-dual subroutine with value $\lambda_1$": it rules out a vacuous reading of (ii). The statement holds for every tie-breaking order and every $\lambda_1 \ge 0$ ("for any fixed $\lambda_1$", p. 7).
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 6, Theorem 1 (proved pp. 7-8, Section 5)

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_potential
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

namespace BudgetedPCTSP.Rooted

/-- Theorem 1 of Paul, Freund, Ferber, Shmoys & Williamson (Math. Oper. Res. 2020), p. 6
(proved pp. 7–8, "for any fixed λ₁"). Fix `λ₁ ≥ 0`.

(i) PD(λ₁) has a complete run.

(ii) Let `y` and `𝒮` come from any complete run of PD(λ₁), under any order of breaking ties. Let
`O⋆` be the vertex set of a feasible tour (a closed walk at the root of cost at most `D`), and
let `O` be a minimal set of `𝒮⁺ = 𝒮 ∪ {V}` containing `O⋆`. Then `|O⋆| ≤ λ₁ D + π(O)`.

The paper takes `O⋆` from an optimal tour; its proof uses only feasibility, so the statement is
made for every feasible tour, which includes the optimal ones. -/
theorem optimal_le_potential_bound {V : Type} [Fintype V] [DecidableEq V] (I : Instance V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ s : PDState V, IsCompleteRun I lam s) ∧
    ∀ s : PDState V, IsCompleteRun I lam s →
      ∀ p : I.G.Walk I.r I.r, I.IsFeasibleTour p →
        ∀ O ∈ sPlus s, p.support.toFinset ⊆ O →
          (∀ O' ∈ sPlus s, p.support.toFinset ⊆ O' → ¬ O' ⊂ O) →
            (p.support.toFinset.card : ℝ) ≤ lam * I.D + potential s.y O := by sorry

end BudgetedPCTSP.Rooted
