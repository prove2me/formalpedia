-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_efficientGF_iff_isGreatest
-- name    : CooperationGraphs.FairRule.efficientGF_iff_isGreatest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:01.010993+00:00
-- url     : https://prove2.me/theorems/0dc92357-8f87-4127-b9d6-1baf53d8c76a
-- title:
--   Proof of Theorem 4, p. 11, (17) — given (16), efficiency (14) holds iff $d(S,g)$ is the largest feasible shift
-- statement:
--   Let $w$ be a game in graph function form and let $Y:GR\to\mathbb R^N$ satisfy (16) with numbers $d(S,g)$: for every graph $g$ and component $S\in N/g$, $Y_n(g)-t_n(g)=d(S,g)$ for all $n\in S$, where $t_n(g)=\sum_{h\subset g}(-1)^{|g|+|h|+1}Y_n(h)$. Then $Y$ satisfies the efficiency condition (14), $(Y_n(g))_{n\in S}\in\partial w(S,g)$ for every $g$ and $S\in N/g$, if and only if
--   $$d(S,g)=\max\{x \mid (x+t_m(g))_{m\in S}\in w(S,g)\}\qquad\text{for all }(S,g)\in ESG.\tag{17}$$
--
--   Together with (16), this reduces the fair allocation rule of a graph function game to the explicit recursion (18).
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. The paper's (17) writes $Y_n(h)$ under the index $m\in S$; we read $Y_m(h)$, as in (18b). "$d(S,g)$ equals the maximum" is stated as "$d(S,g)$ is the greatest element of the set" (`IsGreatest`). The numbers $d(S,g)$ are an arbitrary function of $(g,S)$, read only on embedded subgraphs. $\partial$ is the topological frontier in $\mathbb R^S$.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 4, p. 11, (17)

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, (17): if `Y` satisfies (16) with numbers `d(S,g)`, then `Y` satisfies
the efficiency condition (14) iff for every embedded subgraph `(S, g)`, `d(S,g)` is the maximum of
`{x | (x + t_i(g))_{i ∈ S} ∈ w(S,g)}`. -/
theorem efficientGF_iff_isGreatest {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) (Y : Rule n)
    (d : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hd : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, ∀ i ∈ S, Y g i - altSum Y g i = d g S) :
    IsEfficientGF G Y ↔
      ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g,
        IsGreatest {x : ℝ | (fun i : ↥S => x + altSum Y g i) ∈ G.w g S} (d g S) := by sorry

end CooperationGraphs.FairRule
