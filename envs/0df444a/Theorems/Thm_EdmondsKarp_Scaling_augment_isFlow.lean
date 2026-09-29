-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_augment_isFlow
-- name    : EdmondsKarp.Scaling.augment_isFlow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:24:02.436922+00:00
-- url     : https://prove2.me/theorems/1fcc45f1-7a77-47dc-a8b6-03e1bc8b64ea
-- title:
--   §1.1 — augmenting a flow along an augmenting path gives a flow of value $f(t,s)+\varepsilon$
-- statement:
--   Consider a problem on the network of Figure 1 with capacities $a_i$, $b_j$ and costs $d_{ij}$. Let $f$ be a flow, let $P$ be an augmenting path relative to $f$, and let $\varepsilon = \min_i \varepsilon_i$ be the minimum of the quantities $\varepsilon_i$ along $P$. Then $\varepsilon > 0$, the function $f'$ obtained by augmenting $f$ along $P$ by $\varepsilon$ is a flow, and
--   $$f'(t,s) = f(t,s) + \varepsilon.$$
--
--   This is the statement that an augmentation preserves feasibility and strictly increases the value; it is the elementary step behind every bound on the number of augmentations.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (unnumbered: 'It is easily checked that the f′ thus defined is a flow in N')

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

namespace EdmondsKarp.Scaling

/-- §1.1, p. 249, in the network of Figure 1: if `L` is an augmenting path relative to the flow `x`
and `ε = min ε_i`, then `ε > 0`, the augmented function `f′` is a flow, and
`f′(t, s) = f(t, s) + ε`. -/
theorem augment_isFlow {m n : ℕ} (T : Transport m n) (x : Flow m n) (L : List (Node m n)) (ε : ℝ)
    (hx : IsFlow T x) (hL : IsAugPath T x L) (hε : IsPathMin T x L ε) :
    0 < ε ∧ IsFlow T (augment x L ε) ∧ (augment x L ε).ret = x.ret + ε := by sorry

end EdmondsKarp.Scaling
