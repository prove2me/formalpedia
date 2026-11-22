-- Prove2me | Theorems.Thm_Comp_fixAux_zero
-- name    : Comp.fixAux_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:41:48.177546+00:00
-- url     : https://prove2.me/theorems/586eeda4-050e-4334-bbf4-3390c1d55534
-- title:
--   Comp: fix Aux zero
-- statement:
--   The Comp construction uses the fix Aux zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L74-L74
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L74-L74

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]

theorem Comp.fixAux_zero (f : Finset S → Finset S) (x : Finset S) : fixAux f 0 x = x := by sorry

attribute [defeq] Comp.fixAux_zero
