-- Prove2me | Theorems.Thm_Comp_CsgQ_toPMF_toReal
-- name    : Comp.CsgQ.toPMF_toReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:29.246933+00:00
-- url     : https://prove2.me/theorems/38eeff49-63ab-400a-8237-000187754be8
-- title:
--   Csg Q: to PMF to Real
-- statement:
--   **The first of the two bridge lemmas.** The mass `toPMF` assigns to `s'`, converted back to
--       `ℝ`, is exactly the cast of the rational entry -- so the round trip through `ENNReal` loses
--       nothing. Every later statement relating a rational computation to its real-valued specification
--       goes through this, and none of them unfolds `PMF` again.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L134-L138
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L134-L138

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic
set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.CsgQ

theorem Comp.CsgQ.toPMF_toReal (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    (G.toPMF h s a1 a2 s').toReal = ((G.K s a1 a2 s' : ℚ) : ℝ) := by sorry
