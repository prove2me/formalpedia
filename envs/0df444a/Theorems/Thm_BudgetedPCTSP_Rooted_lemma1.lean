-- Prove2me | Theorems.Thm_BudgetedPCTSP_Rooted_lemma1
-- name    : BudgetedPCTSP.Rooted.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T14:15:40.84032+00:00
-- url     : https://prove2.me/theorems/99bde6e5-0b4c-4ba9-a456-2d3c1dcbbd5a
-- title:
--   Lemma 1 — the duals of PD(λ₁) never overshoot neutrality: 2 Σ_{T ⊆ S} y_T ≤ |S|
-- statement:
--   Fix an instance $(G, c, D, r)$ and $\lambda_1 \ge 0$, and let $y$ be the dual vector at the end of any complete run of the primal-dual subroutine PD($\lambda_1$), under any order of breaking ties. Then for every $S \subseteq V$,
--   $$2 \sum_{T : T \subseteq S} y_T \le |S| ,$$
--   the sum running over all subsets of $S$, including $S$ itself.
--
--   Lemma 1 bounds the dual mass inside any vertex set by half its size. In the proof of Theorem 1 it is applied to the part of the minimal set $O$ that the optimal tour does not visit.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 7, Lemma 1

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

namespace BudgetedPCTSP.Rooted

/-- Lemma 1 of Paul, Freund, Ferber, Shmoys & Williamson (Math. Oper. Res. 2020), p. 7: let `y`
be the dual vector at the end of any run of PD(λ₁), `λ₁ ≥ 0`, under any order of breaking ties.
For any `S ⊆ V`, `2 ∑_{T ⊆ S} y_T ≤ |S|`. -/
theorem lemma1 {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (hlam : 0 ≤ lam) (s : PDState V) (hs : IsCompleteRun I lam s) (S : Finset V) :
    2 * ∑ T ∈ S.powerset, s.y T ≤ (S.card : ℝ) := by sorry

end BudgetedPCTSP.Rooted
