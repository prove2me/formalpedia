-- Prove2me | Theorems.Thm_Erdos393Proof_radical_le_of_dvd
-- name    : Erdos393Proof.radical_le_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:29.430803+00:00
-- url     : https://prove2.me/theorems/10b1229c-9671-4370-9f37-880c1c72edc8
-- title:
--   Erdos393 Proof: radical le of dvd
-- statement:
--   The Erdos393 Proof construction uses the radical le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L74-L76
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L74-L76

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

theorem Erdos393Proof.radical_le_of_dvd {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : radical m ≤ radical n := by sorry
