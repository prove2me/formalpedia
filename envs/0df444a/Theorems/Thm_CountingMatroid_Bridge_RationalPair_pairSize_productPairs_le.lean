-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_RationalPair_pairSize_productPairs_le
-- name    : CountingMatroid.Bridge.RationalPair.pairSize_productPairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:09:10.106204+00:00
-- url     : https://prove2.me/theorems/27cf3788-1361-4120-babd-4ac020b27624
-- title:
--   Finite rational products have linear binary width
-- statement:
--   Let m be the number of factors. If each nonnegative rational is represented by a natural numerator and a positive natural denominator whose combined binary width is at most S, then their unreduced product has combined numerator and denominator width at most 2 + mS. Thus a repeated product of bounded-width factors has linear representation growth.
-- source:
--   A Lean 4.33.1 bit-width proof for unreduced rational-pair multiplication, with no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeRationalPairProducts

set_option autoImplicit false

theorem CountingMatroid.Bridge.RationalPair.pairSize_productPairs_le (xs : List Pair) (S : ℕ)
    (hS : ∀ x ∈ xs, pairSize x ≤ S) :
    pairSize (productPairs xs) ≤ 2 + xs.length * S := by
  sorry
