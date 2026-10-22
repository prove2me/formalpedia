-- Prove2me | Theorems.Thm_BudgetedPCTSP_Rooted_laminar_sPlus
-- name    : BudgetedPCTSP.Rooted.laminar_sPlus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:43:06.700984+00:00
-- url     : https://prove2.me/theorems/6bcde58c-b456-4bb4-8d03-5439c66363fe
-- title:
--   The family 𝒮⁺ of sets ever active in PD(λ₁), together with V, is laminar (p. 6)
-- statement:
--   Fix an instance $(G, c, D, r)$ and $\lambda_1 \ge 0$, and consider any complete run of the primal-dual subroutine PD($\lambda_1$), under any order of breaking ties. Let $\mathcal S$ be the collection of all sets that were active at some moment of the run (including sets active for a period of length zero), and $\mathcal S^+ = \mathcal S \cup \{V\}$. Then $\mathcal S^+$ is **laminar**: for all $A, B \in \mathcal S^+$,
--   $$A \subseteq B \quad\text{or}\quad B \subseteq A \quad\text{or}\quad A \cap B = \emptyset .$$
--
--   Laminarity is what makes "the minimal set of $\mathcal S^+$ containing a given set" well defined, and it is used in the proof of Lemma 1 to partition any set into maximal members of $\mathcal S$.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 6, Section 3 (unnumbered claim: S and S+ are laminar)

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

namespace BudgetedPCTSP.Rooted

/-- Paul, Freund, Ferber, Shmoys & Williamson (Math. Oper. Res. 2020), p. 6: at the end of any
run of PD(λ₁), `λ₁ ≥ 0`, under any order of breaking ties, the family `𝒮⁺ = 𝒮 ∪ {V}` is
laminar: any two of its members are nested or disjoint. -/
theorem laminar_sPlus {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (hlam : 0 ≤ lam) (s : PDState V) (hs : IsCompleteRun I lam s) :
    ∀ A ∈ sPlus s, ∀ B ∈ sPlus s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by sorry

end BudgetedPCTSP.Rooted
