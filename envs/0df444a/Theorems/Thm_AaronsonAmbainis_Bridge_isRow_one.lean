-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_isRow_one
-- name    : AaronsonAmbainis.Bridge.isRow_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:14.130217+00:00
-- url     : https://prove2.me/theorems/c72351c1-f6d5-4228-a84f-76203326d4ba
-- title:
--   Bridge: is Row one
-- statement:
--   The all-ones vector is a row of every `g` at every point (Lemma 2.4 (i) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L52-L61
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L52-L61

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.Bridge.isRow_one (g : Cube ι → Bool) (x : Cube ι) : IsRow g x (fun _ => 1) := by sorry
