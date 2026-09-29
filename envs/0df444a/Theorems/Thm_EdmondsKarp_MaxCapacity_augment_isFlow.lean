-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_augment_isFlow
-- name    : EdmondsKarp.MaxCapacity.augment_isFlow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:18:11.482706+00:00
-- url     : https://prove2.me/theorems/bad08da6-2796-46a1-a4c5-b87ee93e741c
-- title:
--   Augmenting along an augmenting path gives a flow of value $f(t,s)+\varepsilon$
-- statement:
--   Let $f$ be a flow in a network $N$ and let $P$ be an augmenting path relative to $f$, with augmentation $\varepsilon = \min_i \varepsilon_i$. Then $\varepsilon > 0$, the augmented function $f'$ is again a flow in $N$, and
--   $$f'(t,s) = f(t,s) + \varepsilon.$$
--
--   In particular a flow that admits an augmenting path is not maximum. This is the step that makes the labeling method well defined.
--
--   **Formalization Note** Augmenting paths are simple directed $s$–$t$ paths in the residual network $N^f$; the augmentation uses the paper's Case (c) rule for opposite arcs.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (unnumbered: "It is easily checked that the f′ thus defined is a flow in N. Thus, since f′(t, s) = f(t, s) + ε, …")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

/-- §1.1, p. 249: augmenting a flow `f` along an augmenting path `P` gives a flow `f′` in `N`, with
`ε > 0` and `f′(t, s) = f(t, s) + ε`. -/
theorem augment_isFlow {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    IsFlow N (augment N f P) ∧ 0 < pathEps N f P ∧
      augment N f P N.t N.s = f N.t N.s + pathEps N f P := by sorry

end EdmondsKarp.MaxCapacity
