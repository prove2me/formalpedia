-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_Supplement_theorem_1_2
-- name    : ChangingCache.UpperBound.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:41.503313+00:00
-- url     : https://prove2.me/theorems/4d5ffe0f-0239-4795-a232-ad698f8747b8
-- title:
--   Theorem 1.2 — Unbounded ratio and one infinite witness
-- statement:
--   Under memory augmentation two and speed augmentation two, LRU has an unbounded makespan competitive ratio:
--   $$\forall R>0\;\exists m,\sigma:\quad F_{\mathrm{OPT}}(\sigma)>0,\qquad
--   F_{\mathrm{LRU}}(\sigma)>2R\,F_{\mathrm{OPT}}(\sigma).$$
--   Here $m$ is a legal memory profile and $\sigma$ is a nonempty finite request sequence. In addition, there exist a single legal profile $m$, one infinite stream $\tau$, one policy $S$ legal on all its prefixes, and an integer $M$ such that
--   $$\forall r\quad F_S(\tau_{<r})\le M,\qquad
--   \forall q\in\mathbb N\;\exists r\in\mathbb N\quad F_{\mathrm{LRU}}(\tau_{<r})>q.$$
--   Thus the offline optimal total miss count is finite on that one stream, while LRU's is infinite. All policies start empty; each capacity is read at its own miss clock. Neither conclusion assumes a staircase profile or the reduced-run invariant.
--
--   This is a companion theorem to the published upper-bound goal, supported by Lemmas 6.2–6.4. It keeps both the finite multiplicative-ratio clause and the infinite-stream clause.
--
--   Differences from the source:
--   - encoding: unbounded makespan competitive ratio → UnboundedMakespanRatio 2 with every positive real target, positive OPT denominator and cross-multiplied strict inequality; reason: LRU makespan is its miss count divided by two; empty sequences have no positive ratio
--   - encoding: one infinite sequence with finitely many OPT misses and infinitely many LRU misses → one stream, one prefix-consistent legal policy, one uniform natural miss bound, and unbounded LRU prefix counts; reason: existence of a legal finite-total policy is exactly finiteness of the offline optimal total count; incompatible finite policies cannot satisfy these quantifiers
--   - encoding: existential page identifiers → natural page identifiers, without a finite universe bound; reason: the source construction names pages by their first request positions, so these witnesses represent the source construction without restriction
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 2, Theorem 1.2; repeated p. 16; proof pp. 17–20

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Supplement_Streams

namespace ChangingCache.UpperBound.Supplement

/-- Theorem 1.2, pp. 2 and 16: unbounded finite ratios AND a single infinite witness. -/
theorem theorem_1_2 :
    UnboundedMakespanRatio 2 ∧
    ∃ (m : ℕ → ℕ) (σ : ℕ → ℕ) (S : ℕ → Finset ℕ) (M : ℕ),
      IsMemoryProfile m ∧ IsStreamLegal m σ S ∧
      (∀ r, policyMisses (streamPrefix σ r) S r ≤ M) ∧
      (∀ q : ℕ, ∃ r : ℕ, q < (lruRun (augCap 2 2 m) (streamPrefix σ r)).misses) := by sorry

end ChangingCache.UpperBound.Supplement
