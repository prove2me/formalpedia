-- Prove2me | Theorems.Thm_Csg_CSG_B_empty_x
-- name    : Csg.CSG.B_empty_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:15.644439+00:00
-- url     : https://prove2.me/theorems/91d2c77a-13f8-491e-ac20-eb5b7c97eea7
-- title:
--   CSG: B empty x
-- statement:
--   **The payoff, a degeneracy at the escape target.** `B`'s escape test always fails when the
--       target itself is empty: intersecting any support with `∅` is `∅`, so no witness `a1` can ever
--       make the intersection nonempty, regardless of the row-action pool `v1`. Needed wherever a
--       fixed-point iteration for an `Apre1`/`Lpre1`-style operator starts its escape target from `⊥`
--       (i.e. `∅`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeAlmostSure.lean#L94-L99
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeAlmostSure.lean#L94-L99

import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.B_empty_x (v1 : Set A1) (s : S) : C.B v1 (∅ : Set S) s = ∅ := by sorry
