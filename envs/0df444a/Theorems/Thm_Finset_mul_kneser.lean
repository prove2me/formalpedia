-- Prove2me | Theorems.Thm_Finset_mul_kneser
-- name    : Finset.mul_kneser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.171424+00:00
-- url     : https://prove2.me/theorems/ffa02356-b86f-5316-ad33-c9d9e5c4cf3e
-- title:
--   Finset: mul kneser
-- statement:
--   **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
--   stabilizer.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L288-L528
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L288-L528

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

theorem Finset.mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by sorry
