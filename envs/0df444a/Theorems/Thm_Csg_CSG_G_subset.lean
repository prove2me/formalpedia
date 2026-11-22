-- Prove2me | Theorems.Thm_Csg_CSG_G_subset
-- name    : Csg.CSG.G_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:51:47.931801+00:00
-- url     : https://prove2.me/theorems/cc04bde1-b337-4e9e-9678-4218b60988a2
-- title:
--   CSG: G subset
-- statement:
--   **The payoff.** `G safe` always sits inside `safe` itself: unfold `GOrderHom safe`'s own
--       fixed-point equation (`map_gfp`) and discard the `Pre1`-conjunct, since intersecting with
--       `safe` bounds the image regardless of the argument. General infrastructure for worked
--       instances -- e.g. showing a *singleton* candidate is not `G`-forceable reduces to showing the
--       singleton's own `Pre1`-membership fails, once this bounds `G` inside it first.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeSure.lean#L97-L101
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeSure.lean#L97-L101

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_QualitativeSure
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.G_subset (safe : Set S) : C.G safe ⊆ safe := by sorry
