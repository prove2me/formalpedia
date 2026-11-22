-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_lStepF
-- name    : Comp.CsgQ.coe_lStepF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:57:30.501398+00:00
-- url     : https://prove2.me/theorems/1153dc7f-06e1-43fa-88de-68ceeda26584
-- title:
--   Csg Q: coe l Step F
-- statement:
--   `lStepF` is `CSG.LStep`, applied. `coe_bF` inside `coe_aF`; the `change` is only there to strip
--       the `OrderHom` coercion, as `GOrderHom_toCSG` does in `Comp/Qualitative.lean`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L121-L126
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L121-L126

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

theorem Comp.CsgQ.coe_lStepF (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S)
    (w : Finset A1) :
    (↑(G.lStepF x y s w) : Set A1) = (G.toCSG h).LStep ↑x ↑y s ↑w := by sorry
