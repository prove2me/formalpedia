-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_maxAug_gap_le_eps_mul
-- name    : EdmondsKarp.MaxCapacity.maxAug_gap_le_eps_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:20:31.58792+00:00
-- url     : https://prove2.me/theorems/8a9711ba-cc79-4e7f-b35f-62c177580eef
-- title:
--   Maximum augmentation captures a $1/M$ share of the gap: $f^*(t,s) - f^k(t,s) \le \varepsilon^k M$
-- statement:
--   Let $N$ be a network with integer capacities and let $M > 1$ be an integer such that, for every partition of the nodes into $X \ni s$ and $\bar X \ni t$, at most $M$ arcs of $N$ have one end in $X$ and the other in $\bar X$. Let $f^*(t,s)$ be the value of a maximum flow. Let $f^0, \dots, f^K$ be a run of the labeling method in which every augmentation is along an augmenting path giving the maximum possible augmentation, and put $\varepsilon^k = f^{k+1}(t,s) - f^k(t,s)$. Then for every $k < K$,
--   $$f^*(t,s) - f^k(t,s) \;\le\; \varepsilon^k M.$$
--
--   This is the core estimate of the proof of Theorem 2: a maximum augmentation removes at least a fraction $1/M$ of the remaining gap to the optimum.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 254, proof of Theorem 2 (unnumbered display "f*(t, s) − f^k(t, s) ≤ ε^k M")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- Proof of Theorem 2, p. 254: in a run of the labeling method with maximum augmentations, on a
network with integer capacities in which every `s`–`t` cut is crossed by at most `M > 1` arcs, if
`f*(t, s)` is the value of a maximum flow then `f*(t, s) − f^k(t, s) ≤ ε^k M` for every `k < K`,
where `ε^k = f^{k+1}(t, s) − f^k(t, s)`. -/
theorem maxAug_gap_le_eps_mul {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (k : ℕ) (hk : k < K) :
    g N.t N.s - f k N.t N.s ≤ (f (k + 1) N.t N.s - f k N.t N.s) * (M : ℝ) := by sorry

end EdmondsKarp.MaxCapacity
