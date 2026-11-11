-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_4_3
-- name    : DistributedMWC440.UpperBound.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:16.940826+00:00
-- url     : https://prove2.me/theorems/61cc525c-a4d7-46e8-bb5d-8ecbc3269580
-- title:
--   Proposition 4.3 (Distance between cluster center and R)
-- statement:
--   Let $R\subseteq S$ contain at least two vertices and let the truncated shifts capture $R$ at center $s$. Distances to $R$ mean the minimum weighted graph distance to its vertices.
--
--   For the capturing center $s$,
--
--   $$
--   \operatorname{dist}(s,R)<\hat\delta_s-d\le\delta_{\max}-d.
--   $$
--
--   Here $k\ge1/2$, $d>0$, $\delta_{\max}=(k+1+k/\log|S|)d$, and truncated shifts are nonnegative.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: sampled and truncated shifts → explicit nonnegative truncated shifts in the deterministic statement; reason: nonnegativity is the support condition already supplied by the exponential sampling
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 4.3, printed p. 16 / PDF p. 18.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_4_3 {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S R : Finset V) (hR : R ⊆ S) (hcard : 2 ≤ R.card)
    (k d : ℝ) (hk : 1/2 ≤ k) (hd : 0 < d) (δ : Shifts S)
    (hδ : ValidShifts S k d δ) (s : S) (hcapture : Captures W S R k d δ s) :
    setDist W s.val R < trunc S k d δ s - d ∧
      trunc S k d δ s - d ≤ deltaMax S k d - d := by sorry

end DistributedMWC440.UpperBound
