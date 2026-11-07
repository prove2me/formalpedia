-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_nonempty_of_ne
-- name    : AaronsonAmbainis.Bridge.nonempty_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:08.949278+00:00
-- url     : https://prove2.me/theorems/2cd011d1-096f-4ee1-b32a-843103838f6f
-- title:
--   Bridge: nonempty of ne
-- statement:
--   The Bridge construction uses the nonempty of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L163-L166
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L163-L166

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.nonempty_of_ne {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) : Nonempty ι := by sorry
