-- Prove2me | Theorems.Thm_Comp_CsgQ_toCSG_support
-- name    : Comp.CsgQ.toCSG_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:01:15.988199+00:00
-- url     : https://prove2.me/theorems/f7c31b19-8d61-431d-8831-31d3723b7fb5
-- title:
--   Csg Q: to CSG support
-- statement:
--   The cast game's `PMF` support, as the coercion of a `Finset`. `Comp/Qualitative.lean`'s
--       `toPMF_support` composed with `coe_supportF`, in the form the bridges below rewrite with.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L58-L61
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L58-L61

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

theorem Comp.CsgQ.toCSG_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).K s a1 a2).support = (↑(G.supportF s a1 a2) : Set S) := by sorry
