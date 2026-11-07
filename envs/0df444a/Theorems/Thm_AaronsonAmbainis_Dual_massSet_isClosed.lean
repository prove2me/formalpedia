-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_massSet_isClosed
-- name    : AaronsonAmbainis.Dual.massSet_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:10.504541+00:00
-- url     : https://prove2.me/theorems/fd533d33-5328-4ed4-8f6a-51afc36b0c58
-- title:
--   Dual: mass Set is Closed
-- statement:
--   The Dual construction uses the mass Set is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L47-L54
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L47-L54

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Dual.massSet_isClosed (K : ℝ) : IsClosed (massSet ι K) := by sorry
