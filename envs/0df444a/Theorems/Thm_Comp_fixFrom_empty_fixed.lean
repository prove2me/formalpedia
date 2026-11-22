-- Prove2me | Theorems.Thm_Comp_fixFrom_empty_fixed
-- name    : Comp.fixFrom_empty_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:14:08.356126+00:00
-- url     : https://prove2.me/theorems/e1bea76a-0b6a-418f-b259-f9a0fe352761
-- title:
--   Comp: fix From empty fixed
-- statement:
--   The loop from `⊥` always stops at a fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L251-L253
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L251-L253

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.fixFrom_empty_fixed (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f ∅) = fixFrom f ∅ := by sorry
