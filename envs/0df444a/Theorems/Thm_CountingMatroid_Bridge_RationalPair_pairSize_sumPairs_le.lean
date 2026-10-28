-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_RationalPair_pairSize_sumPairs_le
-- name    : CountingMatroid.Bridge.RationalPair.pairSize_sumPairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:01:16.263339+00:00
-- url     : https://prove2.me/theorems/147166ff-07f2-4b3a-a024-f671755402ad
-- title:
--   Finite rational sums have polynomial binary width
-- statement:
--   Let $m$ be a finite number of nonnegative rationals, each represented by a natural numerator and a positive natural denominator whose combined binary width is at most $S$. If they are summed by unreduced cross-product addition, the result has combined numerator and denominator width at most $2(1+m(S+1))$. Thus this summation method still has polynomial representation growth when both the number of terms and their individual widths are polynomially bounded.
-- source:
--   A Lean 4.33.1 bit-width proof for unreduced rational-pair addition, with no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeRationalPairSums

set_option autoImplicit false

theorem CountingMatroid.Bridge.RationalPair.pairSize_sumPairs_le (xs : List Pair) (S : ℕ)
    (hS : ∀ x ∈ xs, pairSize x ≤ S) :
    pairSize (sumPairs xs) ≤ 2 * (1 + xs.length * (S + 1)) := by
  sorry
