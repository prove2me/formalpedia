-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_abs_gadget_le_one
-- name    : AaronsonAmbainis.Row.abs_gadget_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:57.548008+00:00
-- url     : https://prove2.me/theorems/9979189f-2495-46f3-9840-1dda514d70ab
-- title:
--   Row: abs gadget le one
-- statement:
--   The Row construction uses the abs gadget le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L117-L123
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L117-L123

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.abs_gadget_le_one (a : Finset ι → ℝ) (ha : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1)
    (x : Cube ι) (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (w : Cube β) : |gadget a x S m c w| ≤ 1 := by sorry
