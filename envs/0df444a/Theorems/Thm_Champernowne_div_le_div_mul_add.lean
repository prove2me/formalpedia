-- Prove2me | Theorems.Thm_Champernowne_div_le_div_mul_add
-- name    : Champernowne.div_le_div_mul_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:38.696412+00:00
-- url     : https://prove2.me/theorems/e44b2d99-881c-471b-a127-325709efb9b3
-- title:
--   Champernowne: div le div mul add
-- statement:
--   Rounding compatibility: `t/q ≤ t/(p·q)·p + p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L101-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L101-L111

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.div_le_div_mul_add (t p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    t / q ≤ t / (p * q) * p + p := by sorry
