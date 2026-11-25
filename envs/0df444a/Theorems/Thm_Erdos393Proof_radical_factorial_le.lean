-- Prove2me | Theorems.Thm_Erdos393Proof_radical_factorial_le
-- name    : Erdos393Proof.radical_factorial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:48.685804+00:00
-- url     : https://prove2.me/theorems/71ef03ae-526b-4395-ad5c-2b4fa4347781
-- title:
--   Erdos393 Proof: radical factorial le
-- statement:
--   `rad(n!)` is the product of the primes up to `n`, which is at most `4^n`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L91-L97
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L91-L97

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial

theorem Erdos393Proof.radical_factorial_le (n : ℕ) : radical n ! ≤ 4 ^ n := by sorry
