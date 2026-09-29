-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_maximum_augmentation_bound
-- name    : EdmondsKarp.MaxCapacity.maximum_augmentation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:21:51.874406+00:00
-- url     : https://prove2.me/theorems/c3c59597-61a9-4d52-addf-5f9c517df26f
-- title:
--   Theorem 2 — maximum-augmentation paths reach a maximum flow within $1 + \log_{M/(M-1)} f^*(t,s)$ augmentations
-- statement:
--   Let $N$ be a network in which every capacity is an integer. Let $M > 1$ be an integer such that, for every partition of the nodes of $N$ into two sets $X$ and $\bar X$ with $s \in X$ and $t \in \bar X$, the number of arcs of $N$ with one end in $X$ and the other in $\bar X$ is at most $M$. Let $f^*(t,s)$ be the value of a maximum flow in $N$.
--
--   Consider a run of the labeling method: flows $f^0, f^1, \dots, f^K$, where $f^0$ is integer-valued (for instance the zero flow) and, for each $k < K$, $f^{k+1}$ is obtained from $f^k$ by augmenting along an augmenting path relative to $f^k$ that gives the maximum possible augmentation. Then:
--
--   1. the number of augmentations satisfies
--   $$K \;\le\; 1 + \log_{M/(M-1)} f^*(t,s);$$
--   2. if there is no augmenting path relative to $f^K$, then $f^K$ is a maximum flow.
--
--   Together the two parts say that the labeling method with the largest-augmentation rule stops at a maximum flow after at most $1 + \log_{M/(M-1)} f^*(t,s)$ augmentations — a bound that depends on the capacities only logarithmically, in contrast with the bound $f^*(t,s)$ that holds for an arbitrary choice of augmenting paths.
--
--   **Formalization Note** The maximum flow $g$ with $f^*(t,s) = g(t,s)$ is taken as a hypothesis; this is not restrictive, since every network has a maximum flow (the set of flows is nonempty and compact). The logarithm is `Real.logb (M / (M - 1))` with $M$ cast to $\mathbb R$; when $f^*(t,s) = 0$ Lean's `Real.logb` returns $0$ and the bound reads $K \le 1$, which is the paper's statement in that case since no augmentation is then possible. The crossing arcs counted by $M$ are the arcs of $N$, the return arc included (the literal reading of p. 253). The initial flow must be integer-valued on the arcs of $N$; the paper starts from the zero flow (p. 250) and uses its integrality (p. 254).
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 253, §1.3, Theorem 2 (with the hypotheses on N, M and f*(t, s) stated just before it)

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- **Theorem 2** (Edmonds–Karp 1972, p. 253). Let `N` be a network with integer capacities and let
`M > 1` be an integer such that every partition of the nodes into `X ∋ s` and `X̄ ∋ t` has at most `M`
arcs of `N` with one end in `X` and the other in `X̄`; let `f*(t, s)` be the value of a maximum flow.
If the labeling method, started from an integer-valued flow `f^0`, performs `K` augmentations, each
along an augmenting path giving the maximum possible augmentation, then
(a) `K ≤ 1 + log_{M/(M−1)} f*(t, s)`, and
(b) if there is no augmenting path relative to `f^K`, then `f^K` is a maximum flow. -/
theorem maximum_augmentation_bound {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (hint : IsIntegralOn N (f 0)) :
    (K : ℝ) ≤ 1 + Real.logb ((M : ℝ) / ((M : ℝ) - 1)) (g N.t N.s) ∧
      ((¬ ∃ Q : List V, IsAugPath N (f K) Q) → IsMaxFlow N (f K)) := by sorry

end EdmondsKarp.MaxCapacity
