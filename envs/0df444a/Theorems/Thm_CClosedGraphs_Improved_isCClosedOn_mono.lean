-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_isCClosedOn_mono
-- name    : CClosedGraphs.Improved.isCClosedOn_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:14.576952+00:00
-- url     : https://prove2.me/theorems/44103f12-ce58-4ec4-8249-9543354a1a11
-- title:
--   §1.2, p. 3 — c-closedness is hereditary
-- statement:
--   Let $G$ be a graph, $c$ a natural number, and $W'\subseteq W$ vertex sets. If the induced subgraph $G[W]$ is $c$-closed, then so is $G[W']$:
--   $$G[W]\ \text{$c$-closed},\quad W'\subseteq W\ \Longrightarrow\ G[W']\ \text{$c$-closed}.$$
--
--   The paper records this as "the properties of being $c$-closed and weakly $c$-closed are hereditary"; only the $c$-closed half is stated here. It is used whenever the proof of Theorem 3.1 passes to an induced subgraph.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 3, §1.2, paragraph after Definition 1.3

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
theorem isCClosedOn_mono {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ}
    {G : SimpleGraph V} {W W' : Set V} (hW : IsCClosedOn c G W) (hsub : W' ⊆ W) :
    IsCClosedOn c G W' := by sorry
end CClosedGraphs.Improved
