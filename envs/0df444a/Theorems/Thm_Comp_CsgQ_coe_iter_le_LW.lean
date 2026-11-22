-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_iter_le_LW
-- name    : Comp.CsgQ.coe_iter_le_LW
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:07:39.085796+00:00
-- url     : https://prove2.me/theorems/9d42a91f-d59f-4d44-8a67-4ef70a9712ba
-- title:
--   Csg Q: coe iter le LW
-- statement:
--   Every stage of the computed climb from `∅` is a lower bound on `LW x y s`. The mirror of
--       `Comp/QualitativeFinset.lean`'s `G_le_coe_iter`, with the inequality the other way up because
--       this is a least fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L131-L142
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L131-L142

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

theorem Comp.CsgQ.coe_iter_le_LW (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S) (n : ℕ) :
    (↑((G.lStepF x y s)^[n] ∅) : Set A1) ≤ (G.toCSG h).LW ↑x ↑y s := by sorry
