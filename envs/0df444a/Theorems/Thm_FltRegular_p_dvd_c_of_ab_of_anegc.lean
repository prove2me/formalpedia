-- Prove2me | Theorems.Thm_FltRegular_p_dvd_c_of_ab_of_anegc
-- name    : FltRegular.p_dvd_c_of_ab_of_anegc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:15.94083+00:00
-- url     : https://prove2.me/theorems/43cea49e-7172-44eb-a95e-a66a13775b3c
-- title:
--   Flt Regular: p dvd c of ab of anegc
-- statement:
--   The Flt Regular construction uses the p dvd c of ab of anegc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/MayAssume/Lemmas.lean#L39-L54

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

theorem FltRegular.p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by sorry
