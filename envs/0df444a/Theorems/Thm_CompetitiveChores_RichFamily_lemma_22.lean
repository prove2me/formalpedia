-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_22
-- name    : CompetitiveChores.RichFamily.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:36.786113+00:00
-- url     : https://prove2.me/theorems/4f9e13b8-7aaa-40c0-87c6-fcfc52b39c76
-- title:
--   Lemma 22 — agent–item parity: MWW_non-lonely(v) = MWW_non-lonely(v^T)
-- statement:
--   Let $n,m\ge1$ and $v\in\mathbb R^{n\times m}_{<0}$, and let $v^T\in\mathbb R^{m\times n}_{<0}$ be the transposed problem, in which the $m$ chores are agents and the $n$ agents are chores. Identifying a bipartite graph on $([n],[m])$ with the graph on $([m],[n])$ having the same edges,
--   $$\mathrm{MWW}_{non\text{-}lonely}(v)=\mathrm{MWW}_{non\text{-}lonely}(v^T).$$
--
--   For $v^T$, "no lonely agents" means that every chore of $v$ is linked to some agent. The symmetry lets the counting bound for few agents be transferred to few chores, which produces the second term of the minimum in Lemma 23 and Corollary 25.
--
--   **Formalization Note** $n,m\ge1$ are added: the paper's sets of agents and chores are non-empty. For $m=0<n$ the left side is empty while the right side contains the empty graph.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 23, §4.1, Lemma 22

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 22 (agent-item parity), p. 23: `MWW_{non-lonely}(v) = MWW_{non-lonely}(v^T)`, the bipartite
graphs on `([n], [m])` and `([m], [n])` being identified by swapping the ends of each edge. -/
theorem lemma_22 (hn : 0 < n) (hm : 0 < m) (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    transposeGraph '' mwwNonLonely v = mwwNonLonely (transposeValues v) := by sorry

end CompetitiveChores.RichFamily
