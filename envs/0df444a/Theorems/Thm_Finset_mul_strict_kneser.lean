-- Prove2me | Theorems.Thm_Finset_mul_strict_kneser
-- name    : Finset.mul_strict_kneser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.964391+00:00
-- url     : https://prove2.me/theorems/7268014a-4705-56ab-bd2c-272edd83bd5f
-- title:
--   Finset: mul strict kneser
-- statement:
--   The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
--   does not equal the RHS, then it is in fact much smaller.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L534-L539
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L534-L539

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
variable (s t)

theorem Finset.mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) := by sorry
