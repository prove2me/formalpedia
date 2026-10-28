-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_RationalPair_rationalPairOperations_preserve_value
-- name    : CountingMatroid.Bridge.RationalPair.rationalPairOperations_preserve_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:34:33.575707+00:00
-- url     : https://prove2.me/theorems/f14632f3-291c-4d4f-94c3-757cb3c9778c
-- title:
--   Unreduced rational arithmetic is exact
-- statement:
--   For nonnegative rational values represented by natural numerator and positive denominator pairs, addition, multiplication, division by a positive rational, and comparison agree exactly with rational arithmetic. Each operation preserves a positive denominator, so intermediate fractions need not be gcd-normalized.
-- source:
--   Lean 4.33.1 proof using only Mathlib and the unreduced pair definitions; no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeNonnegativeRationalPair

set_option autoImplicit false

theorem CountingMatroid.Bridge.RationalPair.rationalPairOperations_preserve_value (x y : Pair)
    (hx : 0 < x.2) (hy : 0 < y.2) (hyn : 0 < y.1) :
    value (add x y) = value x + value y ∧
    value (mul x y) = value x * value y ∧
    value (div x y) = value x / value y ∧
    (value x < value y ↔ x.1 * y.2 < y.1 * x.2) ∧
    0 ≤ value x ∧
    0 < (add x y).2 ∧ 0 < (mul x y).2 ∧ 0 < (div x y).2 := by
  sorry
