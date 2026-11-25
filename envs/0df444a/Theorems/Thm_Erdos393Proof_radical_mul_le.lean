-- Prove2me | Theorems.Thm_Erdos393Proof_radical_mul_le
-- name    : Erdos393Proof.radical_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:46.022921+00:00
-- url     : https://prove2.me/theorems/fc4d762c-96e0-47c8-8827-4f0eac7e9c05
-- title:
--   Erdos393 Proof: radical mul le
-- statement:
--   The Erdos393 Proof construction uses the radical mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L78-L85
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L78-L85

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

theorem Erdos393Proof.radical_mul_le (a b : ℕ) : radical (a * b) ≤ radical a * radical b := by sorry
