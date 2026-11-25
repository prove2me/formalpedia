-- Prove2me | Theorems.Thm_Erdos393Proof_radical_le_self
-- name    : Erdos393Proof.radical_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:22.31504+00:00
-- url     : https://prove2.me/theorems/8fdb374d-a249-49c3-b73c-5b58b9a19268
-- title:
--   Erdos393 Proof: radical le self
-- statement:
--   The Erdos393 Proof construction uses the radical le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L71-L72
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L71-L72

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

theorem Erdos393Proof.radical_le_self {n : ℕ} (hn : n ≠ 0) : radical n ≤ n := by sorry
