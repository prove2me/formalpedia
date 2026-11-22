-- Prove2me | Theorems.Thm_Comp_coe_empty_le_lfp
-- name    : Comp.coe_empty_le_lfp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:12:00.948255+00:00
-- url     : https://prove2.me/theorems/68202c79-db83-4218-9b3d-169e184c6399
-- title:
--   Comp: coe empty le lfp
-- statement:
--   The usual starting point for an `lfp`: nothing.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L167-L169
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L167-L169

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
omit [Fintype S] [DecidableEq S]

theorem Comp.coe_empty_le_lfp (F : Set S →o Set S) : (↑(∅ : Finset S) : Set S) ≤ F.lfp := by sorry
