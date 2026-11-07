-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_chi_eq_prod_sgn
-- name    : AaronsonAmbainis.Row.chi_eq_prod_sgn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:55:35.062944+00:00
-- url     : https://prove2.me/theorems/17b9495b-7849-4406-9705-3f5ac9bc23e5
-- title:
--   Row: chi eq prod sgn
-- statement:
--   The Row construction uses the chi eq prod sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L40-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L40-L40

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Row.chi_eq_prod_sgn (T : Finset ι) (x : Cube ι) : chi T x = ∏ i ∈ T, sgn (x i) := by sorry
