-- Prove2me | Theorems.Thm_FltRegular_a_not_cong_b
-- name    : FltRegular.a_not_cong_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:21.038191+00:00
-- url     : https://prove2.me/theorems/174a7a4d-eb30-4e05-8cbc-a902dc829c4b
-- title:
--   Flt Regular: a not cong b
-- statement:
--   The Flt Regular construction uses the a not cong b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L56-L82
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L56-L82

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

theorem FltRegular.a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧
        ¬↑p ∣ x * y * z := by sorry
