-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_detInequality_iff_printed
-- name    : AaronsonAmbainis.Bridge.detInequality_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:31:22.966202+00:00
-- url     : https://prove2.me/theorems/416f87c7-5b37-46b3-8ffa-7aaaf18da036
-- title:
--   Bridge: det Inequality iff printed
-- statement:
--   The Bridge construction uses the det Inequality iff printed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L145-L178
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L145-L178

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.detInequality_iff_printed : DetInequality ↔ DetInequalityPrinted := by sorry
