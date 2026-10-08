-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_exists_isGreatest_shift
-- name    : CooperationGraphs.FairRule.exists_isGreatest_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:59.742189+00:00
-- url     : https://prove2.me/theorems/4ed84564-4487-4d6b-b979-ae89ea01fbbb
-- title:
--   Proof of Theorem 4, p. 11 — $\max\{x \mid (x+r_n)_{n\in S}\in w(S,g)\}$ exists
-- statement:
--   Let $w$ be a game in graph function form: for every embedded subgraph $(S,g)$, i.e. every graph $g$ and connected component $S\in N/g$, the set $w(S,g)\subseteq\mathbb R^S$ is closed, comprehensive and a proper subset of $\mathbb R^S$. Then for every embedded subgraph $(S,g)$ and every vector $r=(r_n)_{n\in S}\in\mathbb R^S$, the maximum
--   $$\max\{x\in\mathbb R \mid (x+r_n)_{n\in S}\in w(S,g)\}$$
--   exists.
--
--   This is what makes the recursion (18) of the proof of Theorem 4 well defined: the constant $d(S,g)$ is the largest uniform shift of $t(g)$ that remains feasible.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. "The maximum exists" is stated as the existence of a greatest element (`IsGreatest`) of the set; a greatest element is unique, which is the paper's "uniquely defined".
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 4, p. 11, sentence after (17)

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, sentence after (17): for a game `w` in graph function form, an
embedded subgraph `(S, g)` and any `r ∈ ℝ^S`, the maximum of `{x | (x + r_i)_{i ∈ S} ∈ w(S,g)}`
exists. -/
theorem exists_isGreatest_shift {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) (g : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S ∈ quot univ g) (r : ↥S → ℝ) :
    ∃ x : ℝ, IsGreatest {x : ℝ | (fun i : ↥S => x + r i) ∈ G.w g S} x := by sorry

end CooperationGraphs.FairRule
