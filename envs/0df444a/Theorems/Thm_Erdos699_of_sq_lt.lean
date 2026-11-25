-- Prove2me | Theorems.Thm_Erdos699_of_sq_lt
-- name    : Erdos699.of_sq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:33.605164+00:00
-- url     : https://prove2.me/theorems/c8acd560-6e76-4555-a9b7-4a771e992e8d
-- title:
--   Erdos699: of sq lt
-- statement:
--   Erdős Problem 699 holds whenever `j² < n`.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L163-L170
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L163-L170

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.of_sq_lt :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by sorry
