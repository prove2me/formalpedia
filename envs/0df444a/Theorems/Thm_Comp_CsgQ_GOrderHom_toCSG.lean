-- Prove2me | Theorems.Thm_Comp_CsgQ_GOrderHom_toCSG
-- name    : Comp.CsgQ.GOrderHom_toCSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:36.005947+00:00
-- url     : https://prove2.me/theorems/36931d28-5bd4-4194-bf55-9c192255beb8
-- title:
--   Csg Q: GOrder Hom to CSG
-- statement:
--   The cast game's `GOrderHom` agrees with `GStepQ` pointwise -- `Pre1_toCSG` intersected with
--       `safe`. With this, a rationally-computed candidate for `G safe` can be checked for being a
--       fixed point and, via `OrderHom.eq_gfp_of_fixed_of_ge` together with a chain of steps from `⊤`,
--       identified with `G safe` exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L146-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L146-L149

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

theorem Comp.CsgQ.GOrderHom_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (safe x : Set S) :
    (G.toCSG h).GOrderHom safe x = G.GStepQ safe x := by sorry
