-- Prove2me | Theorems.Thm_Comp_CsgQ_expect_toCSG
-- name    : Comp.CsgQ.expect_toCSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:24.456969+00:00
-- url     : https://prove2.me/theorems/eba3eb27-26a7-419c-a8cd-b61f87bc8b65
-- title:
--   Csg Q: expect to CSG
-- statement:
--   **The second of the two bridge lemmas.** `CSG.expect` of a cast continuation is the cast of
--       `expectQ` -- the rational one-step computation agrees with the real-valued specification on the
--       nose, with no error term. Together with `toPMF_toReal` this is everything the rest of `Comp/`
--       needs about the transition structure.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L156-L163
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L156-L163

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic
set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.CsgQ

theorem Comp.CsgQ.expect_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2)
    (v : S → ℚ) :
    (G.toCSG h).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
      = ((G.expectQ s a1 a2 v : ℚ) : ℝ) := by sorry
