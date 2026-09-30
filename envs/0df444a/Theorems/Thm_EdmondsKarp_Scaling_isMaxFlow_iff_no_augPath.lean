-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_isMaxFlow_iff_no_augPath
-- name    : EdmondsKarp.Scaling.isMaxFlow_iff_no_augPath
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:24:30.660631+00:00
-- url     : https://prove2.me/theorems/0fbb4fe3-f0cc-449c-8603-33243332d786
-- title:
--   §1.1 — a flow in the Hitchcock network is maximum iff there is no augmenting path
-- statement:
--   Consider a problem on the network of Figure 1 with capacities $a_i$, $b_j$. A flow $f$ is a maximum flow if and only if there is no augmenting path relative to $f$.
--
--   In the scaling method each phase stops when no augmenting path exists; this theorem says that it then holds a maximum flow of that phase's problem.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, pp. 249–250, §1.1 (unnumbered: 'the flow f is not maximum. It can be shown that, conversely, a flow f in N is not maximum only if there is an augmenting path with respect to f')

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

namespace EdmondsKarp.Scaling

/-- §1.1, pp. 249–250, in the network of Figure 1: a flow is maximum if and only if there is no
augmenting path relative to it. -/
theorem isMaxFlow_iff_no_augPath {m n : ℕ} (T : Transport m n) (x : Flow m n) (hx : IsFlow T x) :
    IsMaxFlow T x ↔ ¬ ∃ L : List (Node m n), IsAugPath T x L := by sorry

end EdmondsKarp.Scaling
