-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_toDiscountedCSG_toCSG
-- name    : Comp.DiscountedCsgQ.toDiscountedCSG_toCSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:40:23.429105+00:00
-- url     : https://prove2.me/theorems/8cd87656-ae0a-4c7c-8363-a2b20a47d37a
-- title:
--   Discounted Csg Q: to Discounted CSG to CSG
-- statement:
--   The underlying real-valued `CSG` of `toDiscountedCSG` is the one `CsgQ.toCSG` already built --
--       `rfl`, recorded as a lemma so later files can rewrite with it instead of relying on `extends`
--       unfolding at the right moment.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L193-L194
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L193-L194

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic
set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.DiscountedCsgQ

theorem Comp.DiscountedCsgQ.toDiscountedCSG_toCSG (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    (G.toDiscountedCSG h).toCSG = G.toCsgQ.toCSG h.1 := by sorry
