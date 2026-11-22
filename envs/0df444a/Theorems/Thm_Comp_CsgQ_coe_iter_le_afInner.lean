-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_iter_le_afInner
-- name    : Comp.CsgQ.coe_iter_le_afInner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:08:07.393892+00:00
-- url     : https://prove2.me/theorems/fe868605-3fbe-48ef-8b2c-d372a6e76a85
-- title:
--   Csg Q: coe iter le af Inner
-- statement:
--   Every stage of the middle climb from `∅` is a lower bound on the `μX` fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L88-L96
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L88-L96

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_iter_le_afInner (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S) (m : ℕ) :
    (↑((G.afStepF b y)^[m] ∅) : Set S) ≤ ((G.toCSG h).AFInner ↑b ↑y).lfp := by sorry
