-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_restrict_removeLink_le
-- name    : CooperationGraphs.FairRule.restrict_removeLink_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:25.566896+00:00
-- url     : https://prove2.me/theorems/921eb5e3-e9ee-4d25-9b5c-538f47a80967
-- title:
--   Proof of Theorem 3, p. 13 — for superadditive $v$, $(v/g)_S\ge(v/g\setminus n{:}m)_S$, with equality if $n\notin S$
-- statement:
--   Let $v\in\mathbb R^{CL}$ be superadditive, i.e. $v_{S\cup T}\ge v_S+v_T$ for all disjoint nonempty $S,T$. Let $g$ be a graph on $N$ and $n{:}m$ a link of $g$. Then for every coalition $S$,
--   $$(v/g)_S=\sum_{T\in S/g}v_T\;\ge\;\sum_{T\in S/(g\setminus n{:}m)}v_T=(v/g\setminus n{:}m)_S,$$
--   and the inequality is an equality if $n\notin S$.
--
--   Breaking a link can only lower the worth of every coalition in the graph-restricted game, and leaves unchanged the worth of coalitions not containing the endpoint $n$.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. The link and nonempty-coalition conditions come from the paper's context.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 3 (headed "PROOF OF THEOREM 4." in the typescript), p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: if `v` is superadditive then `(v/g)_S ≥ (v/(g \ a,b))_S` for every
coalition `S`, with equality if `a ∉ S`. -/
theorem restrict_removeLink_le {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (hab : g.Adj a b)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    restrict v (removeLink g a b) S ≤ restrict v g S ∧
      (a ∉ S → restrict v (removeLink g a b) S = restrict v g S) := by sorry

end CooperationGraphs.FairRule
