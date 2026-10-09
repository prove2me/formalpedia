-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_lemma_18
-- name    : ExpanderBIS.HardCore.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:43.782985+00:00
-- url     : https://prove2.me/theorems/f75a1120-c9f8-4606-95ee-47aa65a74075
-- title:
--   Lemma 18 — for every independent set I, I ∩ 𝒪 or I ∩ ℰ is small
-- statement:
--   Let $G$ be a bipartite graph with classes $\mathcal O, \mathcal E$ on $n \ge 3$ vertices, and let $\alpha > 0$ be such that $G$ is a bipartite $\alpha$-expander. Then for every independent set $I$ of $G$,
--   $$|I \cap \mathcal O| \le \tfrac12 |\mathcal O| \quad\text{or}\quad |I \cap \mathcal E| \le \tfrac12 |\mathcal E|.$$
--
--   This is what makes the two ground states (all odd, all even) exhaust the independent sets: every independent set is a small deviation from one of them.
--
--   **Formalization Note** The hypothesis $n \ge 3$ is not on the page; it is added because the lemma fails on the edgeless graph with one vertex on each side (there $I = V$ has neither side small, and the expansion condition is vacuous). For $n \ge 3$ the expansion condition excludes every such degenerate case. "Small" is written `2 * #S ≤ #side` in $\mathbb N$, and $I \cap \mathcal E$ is `I \ O`.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 18, Lemma 18

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem lemma_18 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α : ℝ)
    (hα : 0 < α) (hn : 3 ≤ Fintype.card V)
    (hbip : IsBipartiteWrt G O) (hG : IsBipExpander G O α)
    (I : Finset V) (hI : IsIndep G I) :
    2 * #(I ∩ O) ≤ #O ∨ 2 * #(I \ O) ≤ #(univ \ O) := by sorry

end ExpanderBIS.HardCore
