-- Prove2me | Theorems.Thm_Csg_cbExpect_t2b
-- name    : Csg.cbExpect_t2b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:14:19.859778+00:00
-- url     : https://prove2.me/theorems/0f924a88-80ed-48be-a4c2-3d2d3aa8fbb0
-- title:
--   Csg: cb Expect t2b
-- statement:
--   The Csg construction uses the cb Expect t2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L201-L202
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L201-L202

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t2b (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .b a2 v = v .t2 := by sorry
