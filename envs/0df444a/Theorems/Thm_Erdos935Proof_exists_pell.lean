-- Prove2me | Theorems.Thm_Erdos935Proof_exists_pell
-- name    : Erdos935Proof.exists_pell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:40.853028+00:00
-- url     : https://prove2.me/theorems/2d47842b-e332-5266-962f-ffc7b5a0620e
-- title:
--   Erdos935 Proof: exists pell
-- statement:
--   Solutions of $x^2 = 8y^2 + 1$ with $3^{k+1} \mid x$ and $y > k$.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L89-L108
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L89-L108

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.exists_pell (k : ℕ) :
    ∃ x y : ℕ, x ^ 2 = 8 * y ^ 2 + 1 ∧ 3 ^ (k + 1) ∣ x ∧ k < y := by sorry
