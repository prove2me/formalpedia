-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_10
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:01:12.763977+00:00
-- url     : https://prove2.me/theorems/7fdbc5ec-66b1-4a9b-a3a0-516a47850f36
-- title:
--   Theorem 10, p. 44 — binary-feedback first-price bidding forces Ω(T^{2/3}) regret even at fixed value 1
-- statement:
--   There exist absolute constants $a>0$ and $T_0\ge1$ such that for every $T\ge T_0$ and every randomized measurable bidding policy with binary win/loss feedback there is an unknown i.i.d. law $F$ of highest competing bids on $[0,1]$ such that, with the bidder value fixed at $1$,
--   $$T\sup_{b\in[0,1]}\mathbb E_F[(1-b)\mathbb1\{b\ge h\}]-\mathbb E\sum_{t<T}(1-b_t)\mathbb1\{b_t\ge h_t\}\ge aT^{2/3}.$$
--   Bids range over the full interval, and the highest competing bid is not revealed. This supplies the lower bound in Appendix B, including the single-context case.
--
--   **Formalization Note** The asymptotic constant and horizon threshold are chosen before the seed space, seed law, algorithm or competing-bid law. A policy may depend on the announced horizon. There is no finite-grid restriction.
--
--   Differences from the source:
--   - encoding: an Ω lower bound → one absolute positive real constant, then every fixed dimension/graph has a positive horizon threshold, and every larger horizon satisfies the bound; reason: the meaning of the asymptotic rate; constants never depend on the horizon, instance, dimensions or policy
--   - encoding: even if the bidder value is fixed → the value is fixed to 1, as in the proof on p. 44; reason: one fixed-value family already establishes the claimed impossibility, with no restriction on allowable bidding strategies
--   - encoding: any randomized strategy with binary feedback → jointly measurable policies on the continuum [0,1], with an arbitrary independent private seed, past bids and win/loss observations; reason: the seed can contain all private randomness; payment is determined by the bid and win indicator, so the observable history is unchanged
--   - encoding: best fixed bid → a real supremum of expected utilities; reason: the range is nonempty and bounded, and the supremum is attained for the first-price payoff on the compact bid interval
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 44, Theorem 10

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Bidding

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- Theorem 10, p. 44. With bidder value fixed at 1 and win/loss feedback, every
randomized measurable policy has worst-case regret Ω(T^(2/3)) against an unknown
i.i.d. distribution of highest competing bids. The bids remain a continuum. -/
theorem theorem_10 : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, 0 < T₀ ∧
    ∀ T : ℕ, T₀ ≤ T → ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω), IsProbabilityMeasure μ → ∀ A : BidPolicy Ω, A.IsMeasurable →
      ∃ F : Measure Bid, IsProbabilityMeasure F ∧
        c * (T : ℝ) ^ (2 / 3 : ℝ) ≤
          (T : ℝ) * bidOptimalRevenue F - bidAlgorithmRevenue μ A F T := by sorry

end CrossLearnCB.UCB1CL.Supplement
