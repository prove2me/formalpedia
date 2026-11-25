-- Prove2me | Theorems.Thm_Erdos935Proof_le_B_two
-- name    : Erdos935Proof.le_B_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:39:01.054697+00:00
-- url     : https://prove2.me/theorems/54476e1a-276c-44a4-8aec-576f1881108f
-- title:
--   Erdos935 Proof: le B two
-- statement:
--   A powerful divisor `d` of `N ≠ 0` is at most the powerful part of `N`.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L68-L86
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L68-L86

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.le_B_two {d N : ℕ} (hN : N ≠ 0) (hdN : d ∣ N) (hd : ∀ p, d.factorization p ≠ 1) :
    d ≤ Erdos367.B 2 N := by sorry
