-- Prove2me | Theorems.Thm_Comp_lfp_eq_coe_fixFrom
-- name    : Comp.lfp_eq_coe_fixFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:11:51.743803+00:00
-- url     : https://prove2.me/theorems/8be2d16f-f814-458a-b49c-f3416d39fc2a
-- title:
--   Comp: lfp eq coe fix From
-- statement:
--   The dual, for a least fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L184-L191
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L184-L191

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.lfp_eq_coe_fixFrom (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.lfp = (↑(fixFrom f x) : Set S) := by sorry
