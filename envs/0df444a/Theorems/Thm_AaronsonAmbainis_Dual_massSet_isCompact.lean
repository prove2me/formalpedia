-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_massSet_isCompact
-- name    : AaronsonAmbainis.Dual.massSet_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:37.625483+00:00
-- url     : https://prove2.me/theorems/e6feffe7-ac52-4efd-9bc8-bd95f1c3cb3f
-- title:
--   Dual: mass Set is Compact
-- statement:
--   The Dual construction uses the mass Set is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L57-L63
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L57-L63

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Dual.massSet_isCompact (K : ℝ) : IsCompact (massSet ι K) := by sorry
