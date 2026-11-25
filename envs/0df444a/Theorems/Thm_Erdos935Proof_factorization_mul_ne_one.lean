-- Prove2me | Theorems.Thm_Erdos935Proof_factorization_mul_ne_one
-- name    : Erdos935Proof.factorization_mul_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:45.369086+00:00
-- url     : https://prove2.me/theorems/66a1e62d-1a45-433d-9b3f-b97c9b524423
-- title:
--   Erdos935 Proof: factorization mul ne one
-- statement:
--   A product of two nonzero powerful numbers is powerful.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L51-L57
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L51-L57

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.factorization_mul_ne_one {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : ∀ p, a.factorization p ≠ 1) (hb1 : ∀ p, b.factorization p ≠ 1) (p : ℕ) :
    (a * b).factorization p ≠ 1 := by sorry
