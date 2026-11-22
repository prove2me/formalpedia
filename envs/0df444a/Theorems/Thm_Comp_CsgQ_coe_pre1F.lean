-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_pre1F
-- name    : Comp.CsgQ.coe_pre1F
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:06:46.731889+00:00
-- url     : https://prove2.me/theorems/f72efcef-5a17-4722-a5af-b5526b003255
-- title:
--   Csg Q: coe pre1 F
-- statement:
--   The bridge one level up: `pre1F` is `Pre1Q` under `Finset.coe`. Immediate, because the two were
--       written in the same shape -- `coe_supportF` transported across `Finset.coe_subset`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L80-L89
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L80-L89

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_pre1F (G : CsgQ S A1 A2) (x : Finset S) :
    (↑(G.pre1F x) : Set S) = G.Pre1Q ↑x := by sorry
