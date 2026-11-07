-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_orthant_convex
-- name    : AaronsonAmbainis.Dual.orthant_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:34.261194+00:00
-- url     : https://prove2.me/theorems/6c5f001d-474a-490c-a5c2-9306e5721387
-- title:
--   Dual: orthant convex
-- statement:
--   The Dual construction uses the orthant convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L86-L89
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L86-L89

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.orthant_convex : Convex ℝ (orthant ι) := by sorry
