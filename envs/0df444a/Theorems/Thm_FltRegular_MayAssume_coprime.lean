-- Prove2me | Theorems.Thm_FltRegular_MayAssume_coprime
-- name    : FltRegular.MayAssume.coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:17.604146+00:00
-- url     : https://prove2.me/theorems/a0c36f6f-d1f4-4867-b9aa-c1956e7d0881
-- title:
--   May Assume: coprime
-- statement:
--   The May Assume construction uses the coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L16-L35

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_FltRegular_MayAssume_Lemmas
set_option autoImplicit false
@[expose] public section
public section
open Int Finset
open FltRegular
open FltRegular.MayAssume

theorem FltRegular.MayAssume.coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    letI d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 := by sorry
