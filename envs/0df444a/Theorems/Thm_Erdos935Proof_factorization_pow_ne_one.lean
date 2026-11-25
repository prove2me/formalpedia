-- Prove2me | Theorems.Thm_Erdos935Proof_factorization_pow_ne_one
-- name    : Erdos935Proof.factorization_pow_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:50.400294+00:00
-- url     : https://prove2.me/theorems/8f9b0713-97d1-4816-b623-a44df41cfad2
-- title:
--   Erdos935 Proof: factorization pow ne one
-- statement:
--   A `k`-th power with `k ≥ 2` is powerful.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L60-L65
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L60-L65

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.factorization_pow_ne_one (a : ℕ) {k : ℕ} (hk : 2 ≤ k) (p : ℕ) :
    (a ^ k).factorization p ≠ 1 := by sorry
