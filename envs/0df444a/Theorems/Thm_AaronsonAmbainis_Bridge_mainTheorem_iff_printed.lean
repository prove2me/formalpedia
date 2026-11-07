-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_mainTheorem_iff_printed
-- name    : AaronsonAmbainis.Bridge.mainTheorem_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:21.559228+00:00
-- url     : https://prove2.me/theorems/3d3e2642-0257-467a-b5ee-b64be32472fb
-- title:
--   Bridge: main Theorem iff printed
-- statement:
--   The Bridge construction uses the main Theorem iff printed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L245-L246
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L245-L246

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.mainTheorem_iff_printed : MainTheorem ↔ MainTheoremPrinted := by sorry
