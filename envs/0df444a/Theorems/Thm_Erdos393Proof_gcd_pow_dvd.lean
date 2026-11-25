-- Prove2me | Theorems.Thm_Erdos393Proof_gcd_pow_dvd
-- name    : Erdos393Proof.gcd_pow_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:48.202876+00:00
-- url     : https://prove2.me/theorems/217124ce-74ee-4061-9bf8-eb195bb94331
-- title:
--   Erdos393 Proof: gcd pow dvd
-- statement:
--   `gcd(b, a^j)` divides `gcd(b, a)^j`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L102-L109
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L102-L109

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

theorem Erdos393Proof.gcd_pow_dvd (a b : ℕ) : ∀ j : ℕ, Nat.gcd b (a ^ j) ∣ Nat.gcd b a ^ j := by sorry
