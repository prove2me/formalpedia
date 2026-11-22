-- Prove2me | Theorems.Thm_Csg_CSG_A_univ_v2
-- name    : Csg.CSG.A_univ_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:27.252285+00:00
-- url     : https://prove2.me/theorems/226c7373-66e1-4a0f-be58-2979b4bab499
-- title:
--   CSG: A univ v2
-- statement:
--   **The payoff, a degeneracy at the excused-columns argument.** `A`'s safety test always
--       succeeds when every column is already excused: `a2 ∈ v2` holds trivially for any `a2` when
--       `v2 = univ`, so the `∀a2, a2 ∈ v2 ∨ ...` condition needs no support check at all, and holds for
--       *every* row action `a1`. Needed wherever a fixed-point iteration threading a *growing* excused
--       set (`AFV`/`LFV`'s own inner steps) reaches `univ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeAlmostSure.lean#L117-L120
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeAlmostSure.lean#L117-L120

import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.A_univ_v2 (y : Set S) (s : S) : C.A (Set.univ : Set A2) y s = Set.univ := by sorry
