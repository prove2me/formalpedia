-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_chi_mul_chi
-- name    : AaronsonAmbainis.Row.chi_mul_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:33.761337+00:00
-- url     : https://prove2.me/theorems/7efcc89c-21d5-41d7-ae8c-9ec5323ae203
-- title:
--   Row: chi mul chi
-- statement:
--   Characters multiply by symmetric difference.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L61-L68
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L61-L68

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Row.chi_mul_chi [Fintype ι] [DecidableEq ι] (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by sorry
