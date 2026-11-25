-- Prove2me | Theorems.Thm_Erdos393Proof_radical_pow
-- name    : Erdos393Proof.radical_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:47.282769+00:00
-- url     : https://prove2.me/theorems/41b0f1bb-cd45-4552-aa61-3f627ebd66e5
-- title:
--   Erdos393 Proof: radical pow
-- statement:
--   The Erdos393 Proof construction uses the radical pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L87-L88
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L87-L88

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

theorem Erdos393Proof.radical_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) : radical (n ^ k) = radical n := by sorry
