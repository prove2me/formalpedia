-- Prove2me | Theorems.Thm_Erdos699_two_mul_card_le
-- name    : Erdos699.two_mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:00.367292+00:00
-- url     : https://prove2.me/theorems/6775add6-da9b-472b-93b7-51ba32f5de97
-- title:
--   Erdos699: two mul card le
-- statement:
--   A set of primes below `i` has at most `i / 2` elements: `p ↦ (p - 1) / 2` is injective on
--   primes and maps those below `i` into `[0, i / 2)`.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L98-L120
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L98-L120

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.two_mul_card_le {s : Finset ℕ} {i : ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p < i) :
    2 * s.card ≤ i := by sorry
