-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_5_3
-- name    : DistributedMWC440.UpperBound.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:25:55.100676+00:00
-- url     : https://prove2.me/theorems/182f609e-530d-4f69-b03d-8b59ca7643d9
-- title:
--   Lemma 5.3 (Safety preserves cluster assignment)
-- statement:
--   Use the augmented graph with a virtual source and edge lengths $2\delta_{\max}-\hat\delta_s$. Any tree-like approximate SSSP output determines the cluster of a vertex by the first real node on its tree path from the virtual source.
--
--   Assume $k\ge1/2$, $d>0$, $\epsilon>0$, $|S|\ge2$, and nonnegative truncated shifts. If $v$ is $\epsilon$-safe for $s\in S$ and
--
--   $$
--   \operatorname{dist}_G(s,v)-\hat\delta_s\le0,
--   $$
--
--   then the cluster center assigned to $v$ is $s$, for every tree-like $(1+\epsilon)$-approximate SSSP tree of the augmented graph.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: any tree-like approximate SSSP tree → finite labels, parent pointers and depth together with upper bounds along every actual augmented walk; reason: the tree path certifies the lower distance bound; no approximation or clustering conclusion is assumed
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 5.3, printed p. 22 / PDF p. 24.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_5_3 {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S : Finset V) (hS : 2 ≤ S.card) (k d ε : ℝ)
    (hk : 1/2 ≤ k) (hd : 0 < d) (hε : 0 < ε)
    (δ : Shifts S) (hδ : ValidShifts S k d δ) (s : S) (v : V)
    (hsafe : Safe W S k d ε δ s v) (harrival : dist W s.val v - trunc S k d δ s ≤ 0)
    (T : LDDTree W S k d ε δ) : T.center v = some s.val := by sorry

end DistributedMWC440.UpperBound
