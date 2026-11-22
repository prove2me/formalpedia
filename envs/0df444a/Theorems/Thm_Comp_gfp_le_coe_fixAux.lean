-- Prove2me | Theorems.Thm_Comp_gfp_le_coe_fixAux
-- name    : Comp.gfp_le_coe_fixAux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:11:25.615476+00:00
-- url     : https://prove2.me/theorems/b6b71cc3-45de-4c0f-8d64-9cd13b398f59
-- title:
--   Comp: gfp le coe fix Aux
-- statement:
--   Running the loop from a region above the greatest fixed point leaves one above it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L106-L118
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L106-L118

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]

theorem Comp.gfp_le_coe_fixAux (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) :
    F.gfp ≤ (↑(fixAux f n x) : Set S) := by sorry
