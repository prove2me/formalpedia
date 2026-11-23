-- Prove2me | Theorems.Thm_Comp_CsgQ_afInner_eq_coe_of_fixed
-- name    : Comp.CsgQ.afInner_eq_coe_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:31.137684+00:00
-- url     : https://prove2.me/theorems/004921fb-c82f-4eb0-a273-2cd160252678
-- title:
--   Csg Q: af Inner eq coe of fixed
-- statement:
--   A middle chain that was run and seen to stop pins the `μX` fixed point at `y`, exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L99-L106
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L99-L106

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.afInner_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S) (m : ℕ)
    (hiter : (G.afStepF b y)^[m] ∅ = c) (hfix : G.afStepF b y c = c) :
    ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S) := by sorry
