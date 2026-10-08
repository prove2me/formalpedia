-- Prove2me | Theorems.Thm_EffResSparsify_ResistanceSketch_proposition_10
-- name    : EffResSparsify.ResistanceSketch.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:04.839059+00:00
-- url     : https://prove2.me/theorems/a7fd0bdf-a011-494b-9719-ee33377816f2
-- title:
--   Proposition 10 — effective resistances between distinct vertices are at least $2/(nw_{\max})$
-- statement:
--   Let $G=(V,E,w)$ be a connected simple weighted graph on $n$ vertices with positive edge weights, and let $w_{\max}$ be a real number with $w_e\le w_{\max}$ for every edge $e$. Then for all distinct vertices $u\neq v$,
--   $$
--   R_{uv}\ \ge\ \frac{2}{n\,w_{\max}},
--   $$
--   where $R_{uv}=(\chi_u-\chi_v)^{\mathsf T}L^+(\chi_u-\chi_v)$ is the effective resistance between $u$ and $v$.
--
--   The bound compares $G$ with the complete graph $K_n$ all of whose edge weights equal $w_{\max}$, in which every effective resistance between distinct vertices is exactly $2/(nw_{\max})$. In the paper it supplies the lower bound $\|Z(\chi_u-\chi_v)\|^2\ge 2(1-\varepsilon)/(nw_{\max})$ in the proof of Lemma 9.
--
--   **Formalization Note** As printed the proposition is claimed "for all $u,v\in V$"; at $u=v$ it is false, since $R_{uu}=0$, so the statement here requires $u\neq v$ (the only case Lemma 9 uses). It also needs $G$ to be simple: two parallel unit-weight edges between two vertices give $R_{uv}=1/2<1=2/(nw_{\max})$. The paper's $w_{\max}$, the largest edge weight, is one admissible choice of the upper bound $w_{\max}$; any larger bound only weakens the conclusion.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 12, Proposition 10

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph

namespace EffResSparsify.ResistanceSketch

open Matrix

/-- Proposition 10 (p. 12), for distinct vertices: if `G` is a connected simple weighted graph on
`n` vertices and every edge weight is at most `wmax`, then `R_uv ≥ 2/(n wmax)` for all
`u ≠ v`. (As printed, the proposition also claims it for `u = v`, where `R_uu = 0`.) -/
theorem proposition_10 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : WGraph V E) (hconn : G.IsConnected) (hsimple : G.IsSimple)
    (wmax : ℝ) (hwmax : ∀ e, G.w e ≤ wmax) (u v : V) (huv : u ≠ v) :
    2 / ((Fintype.card V : ℝ) * wmax) ≤ G.R u v := by sorry

end EffResSparsify.ResistanceSketch
