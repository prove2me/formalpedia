-- Prove2me | Theorems.Thm_Comp_coe_fixAux_le_lfp
-- name    : Comp.coe_fixAux_le_lfp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:11:38.882433+00:00
-- url     : https://prove2.me/theorems/fc1c709c-f8f9-4d9a-8426-b31c33d0b1b6
-- title:
--   Comp: coe fix Aux le lfp
-- statement:
--   The dual: running the loop from a region below the least fixed point leaves one below it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L121-L133
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L121-L133

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]

theorem Comp.coe_fixAux_le_lfp (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) :
    (↑(fixAux f n x) : Set S) ≤ F.lfp := by sorry
