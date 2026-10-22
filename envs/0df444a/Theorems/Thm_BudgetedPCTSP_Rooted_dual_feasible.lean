-- Prove2me | Theorems.Thm_BudgetedPCTSP_Rooted_dual_feasible
-- name    : BudgetedPCTSP.Rooted.dual_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:57:32.516682+00:00
-- url     : https://prove2.me/theorems/01322adf-f088-4cd4-940b-15b76b393641
-- title:
--   Dual feasibility throughout PD(λ₁): Σ_{S: e ∈ δ(S)} y_S ≤ λ₁ c_e for every edge, and y ≥ 0 (p. 6)
-- statement:
--   Fix an instance $(G, c, D, r)$ and $\lambda_1 \ge 0$. At every moment of every run of the primal-dual subroutine PD($\lambda_1$), under any order of breaking ties (that is, in every state reachable from the start by events), the dual vector $y$ satisfies the dual constraint of every edge,
--   $$\sum_{S : e \in \delta(S)} y_S \le \lambda_1 c_e \qquad \text{for all } e \in E,$$
--   and is nonnegative: $y_S \ge 0$ for all $S \subseteq V$. Here $e \in \delta(S)$ means that $e$ has exactly one endpoint in $S$.
--
--   Together with a suitable $\lambda_2$ this makes $(y, \lambda_1, \lambda_2)$ a feasible solution of the dual linear program of Section 2, which is the weak-duality ingredient of Theorem 1.
--
--   **Formalization Note.** The paper states that the edge constraints "remain satisfied throughout the subroutine" and concludes that $(y,\lambda_1)$ extends to a feasible dual solution, whose constraints include $y_S \ge 0$. Both parts are stated, for every reachable state.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 6, Section 3 (unnumbered claim: dual feasibility throughout the subroutine); dual LP p. 4

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

namespace BudgetedPCTSP.Rooted

/-- Paul, Freund, Ferber, Shmoys & Williamson (Math. Oper. Res. 2020), p. 6: throughout the
primal-dual subroutine PD(λ₁), for any `λ₁ ≥ 0` and any order of breaking ties, the dual
constraint `∑_{S : e ∈ δ(S)} y_S ≤ λ₁ c_e` holds for every edge `e` of `G`, and `y_S ≥ 0` for
every `S ⊆ V`. -/
theorem dual_feasible {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (hlam : 0 ≤ lam) (s : PDState V) (hs : IsReachable I lam s) :
    (∀ e ∈ I.G.edgeSet, edgeLoad s.y e ≤ lam * I.c e) ∧ (∀ S : Finset V, 0 ≤ s.y S) := by sorry

end BudgetedPCTSP.Rooted
