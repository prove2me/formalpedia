-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_flipSet
-- name    : AaronsonAmbainis.Bridge.diffSet_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:53.445199+00:00
-- url     : https://prove2.me/theorems/dd2ae107-07fc-4c74-9414-1cac1faa842e
-- title:
--   Bridge: diff Set flip Set
-- statement:
--   `Δ(x, x^S) = S`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L62-L64
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L62-L64

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by sorry
