-- Prove2me | Theorems.Thm_Csg_cbExpect_t4
-- name    : Csg.cbExpect_t4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:14:19.458802+00:00
-- url     : https://prove2.me/theorems/fe778bd6-ea4b-46f0-8c5a-3ddd5a9315fe
-- title:
--   Csg: cb Expect t4
-- statement:
--   The Csg construction uses the cb Expect t4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L207-L208
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L207-L208

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t4 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t4 a1 a2 v = v .t5 := by sorry
