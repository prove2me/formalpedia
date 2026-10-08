-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_quot_eq_biUnion
-- name    : CooperationGraphs.FairRule.quot_eq_biUnion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:06.747099+00:00
-- url     : https://prove2.me/theorems/4e54f519-c24c-436d-9677-a18e5eab0f8a
-- title:
--   Proof of Theorem 2, p. 12 — $T/g=\bigcup_{S\in N/g}(T\cap S)/g$
-- statement:
--   Let $g$ be a graph on $N$ and $T$ a coalition. Any two players connected in $T$ by $g$ are also connected in $N$ by $g$, so the partition of $T$ into $g$-connected pieces is obtained by cutting each component of $g$ down to $T$:
--   $$T/g=\bigcup_{S\in N/g}(T\cap S)/g .$$
--
--   Consequently $v/g=\sum_{S\in N/g}u^S$, the decomposition of the graph-restricted game used in the proof of Theorem 2.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Partitions are `Finset (Finset (Fin n))` and the union is `Finset.biUnion`. The paper takes $T\in CL$, so $T$ is required to be nonempty.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 2, p. 12

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 12: for every graph `g` and coalition `T`,
`T/g = ⋃_{S ∈ N/g} (T ∩ S)/g`. -/
theorem quot_eq_biUnion {n : ℕ} (hn : 0 < n) (g : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (hT : T.Nonempty) :
    quot T g = (quot univ g).biUnion (fun S => quot (T ∩ S) g) := by sorry

end CooperationGraphs.FairRule
