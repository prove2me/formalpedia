-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_4_7
-- name    : DistributedMWC440.UpperBound.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:24.30881+00:00
-- url     : https://prove2.me/theorems/3f7b2f66-79d0-48ce-83f7-acf7df173f07
-- title:
--   Proposition 4.7 (Probability of the capture event)
-- statement:
--   Use the real exponential shifts, truncation parameters and strict capture event of Definitions 4.2 and 4.4. The set $R$ is a fixed nonempty subset of the candidate centers before the shifts are sampled.
--
--   For $|S|\ge2$, $k\ge1/2$ and $d>0$, set $\beta=\log|S|/(kd)$ and $\delta_{\max}=(k+1+k/\log|S|)d$. Then
--
--   $$
--   \Pr[\mathcal E_{\mathrm{capture}}(R)]\ge (1-1/e)|S|^{-1/k}.
--   $$
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: independent exponential draws indexed by centers → a finite product of Mathlib exponential measures on real shifts; reason: this is the same continuous law; the rate is positive and truncation is kept separate
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 4.7, printed p. 20 / PDF p. 22.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_4_7 {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S R : Finset V) (hS : 2 ≤ S.card) (hR : R ⊆ S) (hne : R.Nonempty)
    (k d : ℝ) (hk : 1/2 ≤ k) (hd : 0 < d) :
    ENNReal.ofReal ((1-Real.exp (-1))*(S.card : ℝ)^(-1/k)) ≤
      shiftLaw S (rate S k d) {δ | ∃ s : S, Captures W S R k d δ s} := by sorry

end DistributedMWC440.UpperBound
