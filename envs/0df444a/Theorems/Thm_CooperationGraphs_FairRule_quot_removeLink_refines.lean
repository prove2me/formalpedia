-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_quot_removeLink_refines
-- name    : CooperationGraphs.FairRule.quot_removeLink_refines
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:33.443156+00:00
-- url     : https://prove2.me/theorems/5dfb00be-4976-4cbf-8f72-8b59f6129285
-- title:
--   Proof of Theorem 3, p. 13 — $S/(g\setminus n{:}m)$ refines $S/g$, with equality if $n\notin S$
-- statement:
--   Let $g$ be a graph on $N$, $n{:}m$ a link of $g$ and $S\in CL$. Then the partition $S/(g\setminus n{:}m)$ refines $S/g$ as a partition of $S$: every block of $S/(g\setminus n{:}m)$ is contained in a block of $S/g$. Moreover, if $n\notin S$, then
--   $$S/(g\setminus n{:}m)=S/g .$$
--
--   Removing a link can only split the connected pieces of a coalition, and cannot affect a coalition that does not contain one of its endpoints.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Refinement is stated as: every block $B$ of $S/(g\setminus n{:}m)$ satisfies $B\subseteq C$ for some block $C$ of $S/g$ (both are partitions of $S$). The link and nonempty-coalition conditions come from the paper's context.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 3 (headed "PROOF OF THEOREM 4." in the typescript), p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: `S/(g \ a,b)` refines `S/g` as a partition of `S`, and
`S/(g \ a,b) = S/g` if `a ∉ S`. -/
theorem quot_removeLink_refines {n : ℕ} (hn : 0 < n) (g : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : g.Adj a b) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∀ B ∈ quot S (removeLink g a b), ∃ C ∈ quot S g, B ⊆ C) ∧
      (a ∉ S → quot S (removeLink g a b) = quot S g) := by sorry

end CooperationGraphs.FairRule
