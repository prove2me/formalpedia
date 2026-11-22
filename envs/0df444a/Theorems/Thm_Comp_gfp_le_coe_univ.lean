-- Prove2me | Theorems.Thm_Comp_gfp_le_coe_univ
-- name    : Comp.gfp_le_coe_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:11:49.17489+00:00
-- url     : https://prove2.me/theorems/6364e7a6-0f47-45b0-bf6a-1daa267fc842
-- title:
--   Comp: gfp le coe univ
-- statement:
--   The usual starting point for a `gfp`: everything.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L161-L163
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L161-L163

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
omit [DecidableEq S]

theorem Comp.gfp_le_coe_univ (F : Set S →o Set S) : F.gfp ≤ (↑(Finset.univ : Finset S) : Set S) := by sorry
