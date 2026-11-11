-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_5_4
-- name    : DistributedMWC440.UpperBound.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:15.895193+00:00
-- url     : https://prove2.me/theorems/44bdd8f1-6fd7-49fe-acfb-97778fb2873a
-- title:
--   Proposition 5.4 (A non-tree edge → a cycle of small weight)
-- statement:
--   Use the local distance labels obtained from the augmented approximate SSSP tree. Basic detection enumerates non-tree edges whose endpoints have the same cluster center and assigns the source sum of two local labels and the edge weight.
--
--   Assume $k\ge1/2$, $d>0$, $\epsilon>0$, nonnegative truncated shifts and
--
--   $$
--   w(C)\le2(d-2\epsilon\delta_{\max}),\qquad R=S\cap V(C),\qquad |R|\ge2.
--   $$
--
--   Suppose $R$ is captured at $s$ and $\{u,v\}$ is a cycle edge whose endpoints are both $\epsilon$-safe for $s$. If that edge is outside the local approximate SSSP tree, basic detection finds a genuine simple cycle with its computed estimate at most
--
--   $$
--   2\delta_{\max}.
--   $$
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: the cycle detection step → enumeration of genuine fundamental cycles with the source local-label weight estimates; reason: the estimate is computed from the supplied tree labels and original edge length, not chosen to satisfy the conclusion
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 5.4, printed p. 24 / PDF p. 26.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_5_4 {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S : Finset V) (C : Cycle W) (k d ε : ℝ)
    (hk : 1/2 ≤ k) (hd : 0 < d) (hε : 0 < ε)
    (δ : Shifts S) (hδ : ValidShifts S k d δ)
    (hcard : 2 ≤ (cycleSkeleton C S).card)
    (hweight : C.weight ≤ 2*(d-2*ε*deltaMax S k d))
    (s : S) (hcapture : Captures W S (cycleSkeleton C S) k d δ s)
    (T : LDDTree W S k d ε δ) (u v : V) (he : s(u,v) ∈ C.walk.edges)
    (hu : Safe W S k d ε δ s u) (hv : Safe W S k d ε δ s v)
    (hnt : ¬T.treeEdge u v) : BasicSuccess T (2*deltaMax S k d) := by sorry

end DistributedMWC440.UpperBound
