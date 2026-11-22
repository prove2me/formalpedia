-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_supportF
-- name    : Comp.CsgQ.coe_supportF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:54.780866+00:00
-- url     : https://prove2.me/theorems/20657dec-9992-4e66-b8d5-cb407b4f1f20
-- title:
--   Csg Q: coe support F
-- statement:
--   `supportF` is `supportQ` under `Finset.coe`. The whole content of the `Finset` layer is that
--       this holds and that everything above it respects coercion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L65-L68
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L65-L68

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    (↑(G.supportF s a1 a2) : Set S) = G.supportQ s a1 a2 := by sorry
