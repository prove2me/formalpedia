-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
-- name    : AaronsonAmbainis.Bridge.card_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:37.805918+00:00
-- url     : https://prove2.me/theorems/4f7bed31-4b76-4bd5-8e56-63333bf29551
-- title:
--   Bridge: card cube
-- statement:
--   The cube over `ι` has `2^n` points.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L81-L84
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L81-L84

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.card_cube : (Fintype.card (Cube ι) : ℝ) = 2 ^ Fintype.card ι := by sorry
