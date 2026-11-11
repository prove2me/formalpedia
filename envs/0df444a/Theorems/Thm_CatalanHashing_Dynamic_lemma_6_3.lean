-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_lemma_6_3
-- name    : CatalanHashing.Dynamic.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:10.446796+00:00
-- url     : https://prove2.me/theorems/a5820176-240a-4538-8b99-0f8c8ea81bb7
-- title:
--   Lemma 6.3 — a buddy allocation of density 2^{−k} succeeds whenever the allocated density, including the new subarray, is at most 1
-- statement:
--   Let the backup table have $m_B=2^K$ cells and let the buddy allocator start with all of $B$ free. In every state reachable by successful allocations (with any admissible choices), an allocation of density $2^{-k}$, $0\le k\le K$, succeeds whenever
--   $$\sum_{B_{k',a}\ \mathrm{allocated}}2^{-k'}\;+\;2^{-k}\;\le\;1,$$
--   that is, some free subarray has depth at most $k$, so an allocation step exists.
--   With the density bound of Lemma 6.4 this guarantees that the density-regulated backup table never runs out of space.
--
--   Differences from the source:
--
--   - reading: "An allocation of density 2^{-k} succeeds" → ∃ s', AllocStep K s k s' in every state s reachable from the initial state (B_{0,0} free) by successful allocations, for k ≤ K with m_B = 2^K; reason: an allocation succeeds when the allocator finds a free subarray of depth at most k; the lemma is about the allocator's own reachable states
--   - encoding: subarray B_{k,a} → the pair (k, a); reason: notation
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 21, Lemma 6.3 (PDF 22)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Buddy

namespace CatalanHashing.Dynamic

/-- Lemma 6.3: in every state the buddy allocator can reach, an allocation of density `2^{-k}`
succeeds whenever the total density of the allocated subarrays plus `2^{-k}` is at most 1. -/
theorem lemma_6_3 (K : ℕ) (s : BuddyState) (hs : BuddyReachable K s) (k : ℕ) (hk : k ≤ K)
    (hdens : s.allocatedDensity + (1 / 2 : ℝ) ^ k ≤ 1) :
    ∃ s', AllocStep K s k s' := by sorry

end CatalanHashing.Dynamic
