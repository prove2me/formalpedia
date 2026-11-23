-- Prove2me | Theorems.Thm_Csg_cbExpect_t2d
-- name    : Csg.cbExpect_t2d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:14:32.239077+00:00
-- url     : https://prove2.me/theorems/c8a38e61-05cd-417b-9441-86de883344ec
-- title:
--   Csg: cb Expect t2d
-- statement:
--   The Csg construction uses the cb Expect t2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L213-L224
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L213-L224

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t2d (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .d a2 v = (v .t1 + v .t3) / 2 := by sorry
