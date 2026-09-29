-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_augment_isFlow
-- name    : EdmondsKarp.ShortestPath.augment_isFlow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:11:10.720287+00:00
-- url     : https://prove2.me/theorems/09ab5c8d-29b3-4559-bbdb-71b0c3d12ccc
-- title:
--   §1.1 — augmentation along an augmenting path yields a flow of value $f(t,s)+\varepsilon$
-- statement:
--   Let $N$ be a network with source $s$, sink $t$ and return arc $(t,s)$, let $f$ be a flow in $N$, and let $P$ be an augmenting path relative to $f$, with $\varepsilon = \min_i \varepsilon_i$ as defined by Cases (a)–(c). Let $f'$ be the function obtained from $f$ by the augmentation along $P$. Then
--
--   $$\varepsilon > 0, \qquad f' \text{ is a flow in } N, \qquad f'(t,s) = f(t,s) + \varepsilon.$$
--
--   This is the step that makes the labeling method well defined: every augmentation produces a flow of strictly larger value.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (unnumbered: "let ε = min ε_i > 0" and "It is easily checked that the f′ thus defined is a flow in N")

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

namespace EdmondsKarp.ShortestPath

/-- §1.1, p. 249: for an augmenting path `P` relative to a flow `f`, `ε = min ε_i > 0`, and the
augmented `f′` is a flow in `N` with `f′(t, s) = f(t, s) + ε`. -/
theorem augment_isFlow {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    0 < pathEps N f P ∧ IsFlow N (augment N f P) ∧
      augment N f P N.t N.s = f N.t N.s + pathEps N f P := by sorry

end EdmondsKarp.ShortestPath
