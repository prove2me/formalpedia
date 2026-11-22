-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_bF
-- name    : Comp.CsgQ.coe_bF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:57:13.175809+00:00
-- url     : https://prove2.me/theorems/c014b312-c56d-47da-9eb8-ecc2daf89503
-- title:
--   Csg Q: coe b F
-- statement:
--   `bF` is `CSG.B`. One step longer than `coe_aF`, because the escape test has to cross the
--       coercion twice: `Finset.coe_inter` to combine the two coerced sets, then `Finset.coe_nonempty`
--       to turn a nonempty coercion into a nonempty `Finset`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L101-L110
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L101-L110

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

theorem Comp.CsgQ.coe_bF (G : CsgQ S A1 A2) (h : G.WellFormed) (v1 : Finset A1) (x : Finset S) (s : S) :
    (↑(G.bF v1 x s) : Set A2) = (G.toCSG h).B ↑v1 ↑x s := by sorry
