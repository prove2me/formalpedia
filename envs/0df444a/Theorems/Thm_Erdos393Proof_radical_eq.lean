-- Prove2me | Theorems.Thm_Erdos393Proof_radical_eq
-- name    : Erdos393Proof.radical_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:08.425799+00:00
-- url     : https://prove2.me/theorems/e8dadd95-da5e-46ed-a3e2-38b36d09a460
-- title:
--   Erdos393 Proof: radical eq
-- statement:
--   The Erdos393 Proof construction uses the radical eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L64-L64
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L64-L64

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

theorem Erdos393Proof.radical_eq (n : ℕ) : radical n = ∏ p ∈ n.primeFactors, p := by sorry
