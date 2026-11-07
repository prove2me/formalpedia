-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sum_weight
-- name    : AaronsonAmbainis.Row.sum_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:35.193854+00:00
-- url     : https://prove2.me/theorems/14575031-9981-47f4-82b1-51ade15cbe49
-- title:
--   Row: sum weight
-- statement:
--   The Row construction uses the sum weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L47-L49
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L47-L49

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Row.sum_weight (u : ι → ℝ) : ∑ z : Cube ι, weight u z = 1 := by sorry
