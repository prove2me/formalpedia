-- Prove2me | Theorems.Thm_Comp_CsgQ_Pre1_toCSG
-- name    : Comp.CsgQ.Pre1_toCSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:06:21.249662+00:00
-- url     : https://prove2.me/theorems/87c45cc2-5f05-4724-bad7-e83886beb07f
-- title:
--   Csg Q: Pre1 to CSG
-- statement:
--   **The payoff.** The cast game's `Pre1` is exactly `Pre1Q` -- so the whole sure-mode fixed-point
--       machinery of `Csg/QualitativeSure.lean` can be computed over `ℚ` and transported back.
--
--       Immediate once the supports agree, because `Pre1Q` was written in `Pre1`'s own shape: the two
--       differ only in how the kernel's support is expressed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L126-L131
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L126-L131

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Qualitative
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.Pre1_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (x : Set S) :
    (G.toCSG h).Pre1 x = G.Pre1Q x := by sorry
