-- Prove2me | Theorems.Thm_Comp_fixAux_succ
-- name    : Comp.fixAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:44.393267+00:00
-- url     : https://prove2.me/theorems/06a8c548-fe22-4151-a138-35ecc23c6cd5
-- title:
--   Comp: fix Aux succ
-- statement:
--   The Comp construction uses the fix Aux succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L76-L77
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L76-L77

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]

theorem Comp.fixAux_succ (f : Finset S → Finset S) (n : ℕ) (x : Finset S) :
    fixAux f (n + 1) x = if f x = x then x else fixAux f n (f x) := by sorry
