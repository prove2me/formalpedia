-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_maxAug_gap_geometric
-- name    : EdmondsKarp.MaxCapacity.maxAug_gap_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:21:20.134334+00:00
-- url     : https://prove2.me/theorems/b2e5050e-4c5d-48a8-b9be-328c2490be9a
-- title:
--   Geometric decay of the gap: $f^*(t,s) - f^k(t,s) \le f^*(t,s)(1 - M^{-1})^k$
-- statement:
--   Under the hypotheses of Theorem 2 — integer capacities, an integer $M > 1$ bounding the number of arcs of $N$ across every partition of the nodes into $X \ni s$ and $\bar X \ni t$, $f^*(t,s)$ the value of a maximum flow, and a run $f^0, \dots, f^K$ of the labeling method with maximum augmentations — for every $k \le K$,
--   $$f^*(t,s) - f^k(t,s) \;\le\; f^*(t,s)\big(1 - M^{-1}\big)^k.$$
--
--   Combined with integrality of the flows, this bounds the index of the last non-maximum flow of the run by $\log_{M/(M-1)} f^*(t,s)$.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 254, proof of Theorem 2 (unnumbered display after "Thus, by induction,")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- Proof of Theorem 2, p. 254: under the hypotheses of Theorem 2, for every `k ≤ K`,
`f*(t, s) − f^k(t, s) ≤ f*(t, s)(1 − M⁻¹)^k`. -/
theorem maxAug_gap_geometric {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (k : ℕ) (hk : k ≤ K) :
    g N.t N.s - f k N.t N.s ≤ g N.t N.s * (1 - (M : ℝ)⁻¹) ^ k := by sorry

end EdmondsKarp.MaxCapacity
