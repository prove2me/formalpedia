-- Prove2me | Theorems.Thm_DynConnWC_theorem_22
-- name    : DynConnWC.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:47.468203+00:00
-- url     : https://prove2.me/theorems/d0270d4b-4005-449d-94c4-7464429b9ed6
-- title:
--   Theorem 22 — on $E_1\cap\dots\cap E_4$, $F_{\mathrm{final}}$ spans $G$ after every update
-- statement:
--   On $E_1\cap E_2\cap E_3\cap E_4$, the forest $F_{\mathrm{final}}$ is a spanning forest of $G_t$ at the end of every update $t$. Hence every connectivity query is answered correctly: for every operation sequence with these updates, a query's two vertices lie in the same tree of $F_{\mathrm{final}}$ exactly when they are connected in the current graph.
--
--   This is invariant I4.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 22, p.22 (PDF 23–24)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Theorem 22 (Spanning invariant).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.22 (PDF 23–24).
"On E1 ∩ E2 ∩ E3 ∩ E4, F_final is a spanning forest of G at the end of every update. Hence every
connectivity query is answered correctly."

**Formalization Note.** The first clause covers `t = 0` too. The second clause is for every sequence of
operations whose updates are `σ`. -/
theorem theorem_22 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf) (R : RandChoices S)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ)
    (hE1 : E1 S R σ) (hE2 : E2 S R σ) (hE3 : E3 S R σ) (hE4 : E4 S R σ) :
    (∀ t, t ≤ σ.length → IsSpanningForestOf (stateAt S R σ t).Ffin (Gt σ t)) ∧
    (∀ ops : List (Op n), updatesOf ops = σ → AlgAllCorrect S R ops) := by sorry

end DynConnWC
