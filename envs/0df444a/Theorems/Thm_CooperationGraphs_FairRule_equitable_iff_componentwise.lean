-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_equitable_iff_componentwise
-- name    : CooperationGraphs.FairRule.equitable_iff_componentwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:24.852542+00:00
-- url     : https://prove2.me/theorems/27686400-ca5b-4e2f-8cbf-0582d2a94274
-- title:
--   Proof of Theorem 4, p. 11, (16) — equity holds iff $Y_n(g)-t_n(g)$ is constant on components
-- statement:
--   For a function $Y:GR\to\mathbb R^N$ and a graph $g$, write $t_n(g)=\sum_{h\subset g}(-1)^{|g|+|h|+1}Y_n(h)$, the sum over strict subgraphs $h$ of $g$. Then $Y$ satisfies the equity condition (10),
--   $$Y_n(g)-Y_n(g\setminus n{:}m)=Y_m(g)-Y_m(g\setminus n{:}m)\qquad\text{for all } g\in GR \text{ and all links } n{:}m\in g,$$
--   if and only if, for every graph $g$ and every connected component $S\in N/g$, there is a number $d(S,g)$ with
--   $$Y_n(g)-t_n(g)=d(S,g)\qquad\text{for all } n\in S.\tag{16}$$
--
--   This characterization turns equity into a recursion in the number of links: $Y(g)$ is determined by the values on strict subgraphs up to one constant per component.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. $t_n(g)$ is `altSum Y g n`; $N/g$ is `quot univ g`; links are `g.Adj a b`.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 4, p. 11, (15)–(16)

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, (16): a rule `Y` satisfies the equity condition (10) iff for every
graph `g` and every component `S ∈ N/g` there is a number `d(S,g)` with
`Y_i(g) − t_i(g) = d(S,g)` for all `i ∈ S`. -/
theorem equitable_iff_componentwise {n : ℕ} (hn : 0 < n) (Y : Rule n) :
    IsEquitable Y ↔ ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g,
      ∃ d : ℝ, ∀ i ∈ S, Y g i - altSum Y g i = d := by sorry

end CooperationGraphs.FairRule
