-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_slackImage_convex
-- name    : AaronsonAmbainis.Dual.slackImage_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:43.961065+00:00
-- url     : https://prove2.me/theorems/8b5f9479-1109-4f86-8459-0a33d4a7f711
-- title:
--   Dual: slack Image convex
-- statement:
--   The Dual construction uses the slack Image convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L71-L78
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L71-L78

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Dual.slackImage_convex (t : Finset ι → ℝ) (K : ℝ) :
    Convex ℝ (slack t '' massSet ι K) := by sorry
