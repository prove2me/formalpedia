-- Prove2me | Theorems.Thm_Csg_CSG_subset_SF
-- name    : Csg.CSG.subset_SF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:51:42.740777+00:00
-- url     : https://prove2.me/theorems/72ab28b8-51a3-4b7b-bf6e-7c53027349df
-- title:
--   CSG: subset SF
-- statement:
--   **The payoff, dual to `G_subset`.** `b` always sits inside `SF b`: unfold `SFOrderHom b`'s own
--       fixed-point equation (`map_lfp`) and discard the `Pre1`-disjunct, since unioning with `b`
--       bounds the image from below regardless of the argument. Makes "already inside `b`" a trivial
--       corollary of `SF`/`SFG` -- reaching (or eventually always holding) a set you already occupy
--       needs no strategy at all.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeSure.lean#L122-L126
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeSure.lean#L122-L126

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_QualitativeSure
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.subset_SF (b : Set S) : b ⊆ C.SF b := by sorry
