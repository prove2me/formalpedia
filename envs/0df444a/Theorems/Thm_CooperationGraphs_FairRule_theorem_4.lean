-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_theorem_4
-- name    : CooperationGraphs.FairRule.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:10.009554+00:00
-- url     : https://prove2.me/theorems/19193641-5b56-4e49-a497-7d2e1cb9c43e
-- title:
--   Theorem 4 — every game in graph function form has a unique fair allocation rule
-- statement:
--   Let $w$ be a game in graph function form on a finite player set $N$: for every graph $g$ on $N$ and every connected component $S\in N/g$, $w(S,g)\subseteq\mathbb R^S$ is a closed, comprehensive, proper subset of $\mathbb R^S$. Then there is a unique function $Y:GR\to\mathbb R^N$ satisfying the efficiency condition
--   $$(Y_n(g))_{n\in S}\in\partial w(S,g)\qquad\text{for all } g\in GR,\ S\in N/g,\tag{14}$$
--   and the equity condition
--   $$Y_n(g)-Y_n(g\setminus n{:}m)=Y_m(g)-Y_m(g\setminus n{:}m)\qquad\text{for all } g\in GR,\ n{:}m\in g.\tag{10}$$
--
--   This is the non-transferable-utility generalization of Theorem 1: a characteristic function game $v$ is the graph function game $w(S,g)=\{r\in\mathbb R^S\mid\sum_{n\in S}r_n\le v_S\}$.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. $\partial$ is the topological frontier in $\mathbb R^S$ = `↥S → ℝ`. Uniqueness is among all functions $Y:GR\to\mathbb R^N$; condition (7) is not imposed (it is replaced by (14)). The paper's $N$ is nonempty; for $N=\emptyset$ the statement holds trivially, so no nonemptiness hypothesis is needed.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), Theorem 4, p. 10

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 4 (p. 10): every game `w` in graph function form has a unique fair allocation rule
`Y : GR → ℝ^N`, i.e. a unique `Y` satisfying the efficiency condition (14) and the equity
condition (10). -/
theorem theorem_4 {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) :
    ∃! Y : Rule n, IsEfficientGF G Y ∧ IsEquitable Y := by sorry

end CooperationGraphs.FairRule
