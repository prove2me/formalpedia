-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_allPairs_iff_nonconstant
-- name    : AaronsonAmbainis.Bridge.allPairs_iff_nonconstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:30:33.293299+00:00
-- url     : https://prove2.me/theorems/6dd8851f-3214-4ca2-a8eb-1ce782ac120f
-- title:
--   Bridge: all Pairs iff nonconstant
-- statement:
--   The Bridge construction uses the all Pairs iff nonconstant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L198-L227
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L198-L227

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.allPairs_iff_nonconstant : AllPairsInequality ↔ AllPairsNonconstant := by sorry
