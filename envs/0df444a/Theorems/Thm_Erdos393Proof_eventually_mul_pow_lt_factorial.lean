-- Prove2me | Theorems.Thm_Erdos393Proof_eventually_mul_pow_lt_factorial
-- name    : Erdos393Proof.eventually_mul_pow_lt_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:32:06.979543+00:00
-- url     : https://prove2.me/theorems/4e1fb419-c4d1-4b89-bedb-5f42f7754266
-- title:
--   Erdos393 Proof: eventually mul pow lt factorial
-- statement:
--   `n!` grows faster than any exponential.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L127-L135
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L127-L135

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

theorem Erdos393Proof.eventually_mul_pow_lt_factorial (K X : ℕ) : ∀ᶠ n in atTop, K * X ^ n < n ! := by sorry
