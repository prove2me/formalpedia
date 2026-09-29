-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_isMaxFlow_iff_no_augPath
-- name    : EdmondsKarp.MaxCapacity.isMaxFlow_iff_no_augPath
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:18:58.97419+00:00
-- url     : https://prove2.me/theorems/5cd9da8d-58e4-4a7e-af0c-9d5be6eff566
-- title:
--   A flow is maximum if and only if it admits no augmenting path
-- statement:
--   Let $f$ be a flow in a network $N$. Then
--   $$f \text{ is a maximum flow} \iff \text{there is no augmenting path relative to } f.$$
--
--   The direction "$\Rightarrow$" follows from the augmentation step; the direction "$\Leftarrow$" is the classical Ford–Fulkerson converse, which the paper quotes. It guarantees that the labeling method stops only at a maximum flow.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, pp. 249–250, §1.1 (unnumbered: "It can be shown that, conversely, a flow f in N is not maximum only if there is an augmenting path with respect to f.")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

/-- §1.1, pp. 249–250: a flow `f` in `N` is maximum if and only if there is no augmenting path with
respect to `f`. -/
theorem isMaxFlow_iff_no_augPath {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ∃ P : List V, IsAugPath N f P := by sorry

end EdmondsKarp.MaxCapacity
