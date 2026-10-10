-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_7
-- name    : CircStability.Main.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:18.85198+00:00
-- url     : https://prove2.me/theorems/1e31f208-eaf3-499c-b7e3-afb2e5b6d1fa
-- title:
--   Lemma 2.7 — a locally maximal cycle C of G stays locally maximal in the C-closure of G
-- statement:
--   Let $G$ be a graph and $C$ a locally maximal cycle of $G$. Then $C$ is also a locally maximal cycle of the $C$-closure $\overline G$ of $G$:
--
--   $$
--   C \text{ locally maximal in } G\ \Longrightarrow\ C \text{ locally maximal in } \overline G .
--   $$
--
--   This lets the proof of Theorem 4.1 pass from $G$ to $\overline G$, whose induced graph on $V(C)$ is $(c+1)$-closed.
--
--   **Formalization Note.** Since $G\subseteq\overline G$, the cycle $C$ of $G$ is regarded as a cycle of $\overline G$ by mapping it along the inclusion (Mathlib's `Walk.mapLe`).
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 9, Lemma 2.7

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_7 (n : ℕ) (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u)
    (hC : IsLocallyMaximal G C) :
    IsLocallyMaximal (cClosure G C.support.toFinset)
      (C.mapLe (fun _ _ h => Or.inl h : G ≤ cClosure G C.support.toFinset)) := by sorry

end CircStability.Main
