-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_twoSidedMinCost_of_twoSided
-- name    : AaronsonAmbainis.Bridge.twoSidedMinCost_of_twoSided
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:30:58.524311+00:00
-- url     : https://prove2.me/theorems/fe9e8592-0b8c-4546-89fb-5d0da84ed7e8
-- title:
--   Bridge: two Sided Min Cost of two Sided
-- statement:
--   `TwoSidedInequality` gives the form with the least cost as well (take rows of least cost). The
--   converse would need the existence of a row of least cost (compactness); it is not formalised
--   here.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L115-L120
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean#L115-L120

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.twoSidedMinCost_of_twoSided (h : TwoSidedInequality) : TwoSidedMinCost := by sorry
