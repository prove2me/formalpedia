-- Prove2me | Theorems.Thm_CriticalPortraits_d_dvd_choose
-- name    : CriticalPortraits.d_dvd_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:32:03.759199+00:00
-- url     : https://prove2.me/theorems/3c9c0ba2-b5ea-42fa-b1ea-1335ece99d91
-- title:
--   Critical Portraits: d dvd choose
-- statement:
--   **Exactness of the `/ d`.** The denominator divides the numerator: `d ∣ C(d*m, d-1)`. Hence the
--   `/ d` in `card_portraits` is *exact* `ℕ`-division (the count is a genuine integer), not floor
--   rounding — the witness is the portrait count itself, read off `card_portraits_mul`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L69-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L69-L71

module
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Census
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset

theorem CriticalPortraits.d_dvd_choose {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d ∣ (d * m).choose (d - 1) := by sorry
