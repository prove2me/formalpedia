-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_orthant_isClosed
-- name    : AaronsonAmbainis.Dual.orthant_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:44.340879+00:00
-- url     : https://prove2.me/theorems/a67d69bf-6447-4d87-abcd-46cc1629d16b
-- title:
--   Dual: orthant is Closed
-- statement:
--   The Dual construction uses the orthant is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L92-L97
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L92-L97

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.orthant_isClosed : IsClosed (orthant ι) := by sorry
