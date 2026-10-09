-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_sparse_card_le
-- name    : ExpanderBIS.HardCore.sparse_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:14.171795+00:00
-- url     : https://prove2.me/theorems/015ac635-5037-42f9-92f1-e2f9c7db98cf
-- title:
--   §4.1, p. 20 — every sparse independent set satisfies (2 + α)|I| ≤ n
-- statement:
--   Let $G$ be a bipartite $\alpha$-expander ($\alpha > 0$) with classes $\mathcal O, \mathcal E$ on $n$ vertices. If $I$ is an independent set with $I \cap \mathcal O$ and $I \cap \mathcal E$ both sparse, then
--   $$(2+\alpha)\,|I| \le n.$$
--
--   Sparse independent sets are therefore much smaller than the ground states, which have about $n/2$ vertices; this is the size gap that makes their total contribution negligible in Lemma 20.
--
--   **Formalization Note** The paper writes the strict inequality $|I| < n/(2+\alpha)$, derived from strict expansion inequalities $|\partial(I \cap \mathcal E)| > (1+\alpha)|I \cap \mathcal E|$, which fail when $I \cap \mathcal E = \emptyset$. The strict conclusion is false: the 6-cycle is a bipartite $1$-expander, and an even vertex together with the odd vertex opposite it is a sparse independent set with $|I| = 2 = n/(2+\alpha)$. The non-strict form stated here is what expansion gives and suffices for Lemma 20.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 20, §4.1, proof of Lemma 20, display "|I| < n/(2 + α)"

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem sparse_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α : ℝ)
    (hα : 0 < α) (hbip : IsBipartiteWrt G O) (hG : IsBipExpander G O α)
    (I : Finset V) (hI : IsIndep G I)
    (hO : IsSparse G O (I ∩ O)) (hE : IsSparse G (univ \ O) (I \ O)) :
    (2 + α) * (#I : ℝ) ≤ (Fintype.card V : ℝ) := by sorry

end ExpanderBIS.HardCore
