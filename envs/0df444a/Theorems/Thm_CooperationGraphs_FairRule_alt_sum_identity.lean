-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_alt_sum_identity
-- name    : CooperationGraphs.FairRule.alt_sum_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:53.274462+00:00
-- url     : https://prove2.me/theorems/d067a656-8fdf-491f-9d4b-112d6badef49
-- title:
--   Proof of Theorem 4, p. 11 — the alternating-sum identity over subgraphs containing a link
-- statement:
--   Let $Y:GR\to\mathbb R^N$ be any function from graphs to payoff vectors, let $g$ be a graph and let $n{:}m\in g$ be a link of $g$. Write $|h|$ for the number of links of a graph $h$ and $h\subset g$ for a strict subgraph. Then
--   $$\sum_{\substack{h\subseteq g\\ n{:}m\in h}}(-1)^{|g|+|h|}\big(Y_n(h)-Y_n(h\setminus n{:}m)\big)=\sum_{h\subseteq g}(-1)^{|g|+|h|}Y_n(h)=Y_n(g)-\sum_{h\subset g}(-1)^{|g|+|h|+1}Y_n(h).$$
--
--   This identity rewrites the equity condition (10), summed with alternating signs over the subgraphs of $g$ that contain the link, as a condition on $Y_n(g)$ alone; it is the first step of the proof of Theorem 4.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Graphs are `SimpleGraph (Fin n)`, $h\subseteq g$ is `h ≤ g`, $h\subset g$ is `h < g`, and the last sum is the defined quantity $t_n(g)$ (`altSum`). Both equalities are stated, as a conjunction.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 4, p. 11, display before (15)

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, display before (15): for any `Y`, any graph `g` and any link
`a,b ∈ g`, the alternating sum over the subgraphs `h ⊆ g` containing `a,b` of `Y_a(h) − Y_a(h \ a,b)`
equals the alternating sum over all `h ⊆ g` of `Y_a(h)`, which equals `Y_a(g) − t_a(g)`. -/
theorem alt_sum_identity {n : ℕ} (hn : 0 < n) (Y : Rule n) (g : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : g.Adj a b) :
    (∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g ∧ h.Adj a b),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * (Y h a - Y (removeLink h a b) a)) =
      ∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * Y h a ∧
    (∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * Y h a) =
      Y g a - altSum Y g a := by sorry

end CooperationGraphs.FairRule
