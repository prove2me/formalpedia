-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_twoSided_iff_printed
-- name    : AaronsonAmbainis.Bridge.twoSided_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:11:50.711465+00:00
-- url     : https://prove2.me/theorems/28ebfac3-f6ed-4225-8482-1ec382ccbfbf
-- title:
--   Bridge: two Sided iff printed
-- statement:
--   The Bridge construction uses the two Sided iff printed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L52-L96
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L52-L96

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.twoSided_iff_printed : TwoSidedInequality ↔ TwoSidedPrinted := by sorry
