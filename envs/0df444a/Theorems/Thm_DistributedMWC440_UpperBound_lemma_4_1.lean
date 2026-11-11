-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_4_1
-- name    : DistributedMWC440.UpperBound.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:16.310514+00:00
-- url     : https://prove2.me/theorems/e833ebd4-4389-46f7-bdce-2fd8ad0b33f9
-- title:
--   Lemma 4.1 (Probability of no truncation)
-- statement:
--   Let $S$ be the candidate centers, $|S|\ge2$, $k\ge1/2$, and $d>0$. Set $\beta=\log|S|/(kd)$ and $\delta_{\max}=(k+1+k/\log|S|)d$. Sample independent real exponential shifts of rate $\beta$ and truncate each at $\delta_{\max}$.
--
--   The no-truncation probability satisfies the full equality and bound
--
--   $$
--   \Pr[\forall s\in S,\ \hat\delta_s=\delta_s]
--   =\Pr[\forall s\in S,\ \delta_s\le\delta_{\max}]
--   \ge 1-\frac1e |S|^{-1/k}.
--   $$
--
--   Differences from the source:
--   - encoding: independent exponential draws indexed by centers → a finite product of Mathlib exponential measures on real shifts; reason: this is the same continuous law; the rate is positive and truncation is kept separate
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 4.1, printed p. 15 / PDF p. 17.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_4_1 {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : 2 ≤ S.card) (k d : ℝ) (hk : 1/2 ≤ k) (hd : 0 < d) :
    shiftLaw S (rate S k d) {δ | ∀ s, trunc S k d δ s = δ s} =
      shiftLaw S (rate S k d) {δ | ∀ s, δ s ≤ deltaMax S k d} ∧
    ENNReal.ofReal (1 - Real.exp (-1) * (S.card : ℝ)^(-1/k)) ≤
      shiftLaw S (rate S k d) {δ | ∀ s, δ s ≤ deltaMax S k d} := by sorry

end DistributedMWC440.UpperBound
