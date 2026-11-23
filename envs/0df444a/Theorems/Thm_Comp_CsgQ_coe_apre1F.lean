-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_apre1F
-- name    : Comp.CsgQ.coe_apre1F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:07:48.679361+00:00
-- url     : https://prove2.me/theorems/9f84ad88-40a5-4aca-8370-986532623296
-- title:
--   Csg Q: coe apre1 F
-- statement:
--   `apre1F` is `CSG.Apre1`, unconditionally -- no witness family, so no hypothesis.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L70-L74
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L70-L74

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_apre1F (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) :
    (↑(G.apre1F x y) : Set S) = (G.toCSG h).Apre1 ↑x ↑y := by sorry
