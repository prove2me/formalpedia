-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_aF
-- name    : Comp.CsgQ.coe_aF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:01:31.010818+00:00
-- url     : https://prove2.me/theorems/46d48ede-c33c-4e05-af1e-43fb8930ab6f
-- title:
--   Csg Q: coe a F
-- statement:
--   `aF` is `CSG.A`. Both were written in the same shape, so this is `toCSG_support` transported
--       across `Finset.coe_subset`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L79-L83
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L79-L83

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_aF (G : CsgQ S A1 A2) (h : G.WellFormed) (v2 : Finset A2) (y : Finset S) (s : S) :
    (↑(G.aF v2 y s) : Set A1) = (G.toCSG h).A ↑v2 ↑y s := by sorry
