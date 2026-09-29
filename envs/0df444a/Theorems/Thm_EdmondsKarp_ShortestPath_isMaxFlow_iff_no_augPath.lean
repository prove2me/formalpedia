-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_isMaxFlow_iff_no_augPath
-- name    : EdmondsKarp.ShortestPath.isMaxFlow_iff_no_augPath
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:11:40.325194+00:00
-- url     : https://prove2.me/theorems/7fa70f3c-7a2b-4423-b9c8-962d7428ca6f
-- title:
--   §1.1 — a flow is maximum iff it admits no augmenting path
-- statement:
--   Let $N$ be a network with source $s$, sink $t$ and return arc $(t,s)$, and let $f$ be a flow in $N$. Then
--
--   $$f \text{ is a maximum flow} \iff \text{there is no augmenting path relative to } f.$$
--
--   The direction "$\Rightarrow$" holds because augmenting along a path increases $f(t,s)$; the direction "$\Leftarrow$" is the statement that a flow is not maximum only if there is an augmenting path. It justifies the stopping rule of the labeling method: the method stops exactly at a maximum flow.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, pp. 249–250, §1.1 (unnumbered: "Thus, since f′(t, s) = f(t, s) + ε, the flow f is not maximum. It can be shown that, conversely, …")

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

namespace EdmondsKarp.ShortestPath

/-- §1.1, pp. 249–250: a flow `f` in `N` is a maximum flow if and only if there is no augmenting path
relative to `f`. -/
theorem isMaxFlow_iff_no_augPath {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ∃ P : List V, IsAugPath N f P := by sorry

end EdmondsKarp.ShortestPath
