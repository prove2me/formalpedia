-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_slackImage_isCompact
-- name    : AaronsonAmbainis.Dual.slackImage_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:27.81548+00:00
-- url     : https://prove2.me/theorems/485a5482-83e9-46a1-b779-1a36a74306b0
-- title:
--   Dual: slack Image is Compact
-- statement:
--   The Dual construction uses the slack Image is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L81-L83
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L81-L83

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Dual.slackImage_isCompact (t : Finset ι → ℝ) (K : ℝ) :
    IsCompact (slack t '' massSet ι K) := by sorry
