-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_massSet_convex
-- name    : AaronsonAmbainis.Dual.massSet_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:17.765637+00:00
-- url     : https://prove2.me/theorems/5756ba7a-6f51-4641-8aee-1fa3c44af3ff
-- title:
--   Dual: mass Set convex
-- statement:
--   The Dual construction uses the mass Set convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L34-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean#L34-L44

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Dual.massSet_convex (K : ℝ) : Convex ℝ (massSet ι K) := by sorry
