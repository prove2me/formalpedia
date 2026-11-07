-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_influence_iff_printed
-- name    : AaronsonAmbainis.Bridge.influence_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:08.254113+00:00
-- url     : https://prove2.me/theorems/df14964a-0a37-472b-be37-e73c784b3124
-- title:
--   Bridge: influence iff printed
-- statement:
--   The Bridge construction uses the influence iff printed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L157-L168
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L157-L168

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.influence_iff_printed : InfluenceBound ↔ InfluencePrinted := by sorry
