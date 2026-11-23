-- Prove2me | Theorems.Thm_Csg_cbExpect_t3d
-- name    : Csg.cbExpect_t3d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:15:14.488813+00:00
-- url     : https://prove2.me/theorems/bd346cb9-16bd-47a2-9e8a-1a960d06276e
-- title:
--   Csg: cb Expect t3d
-- statement:
--   The Csg construction uses the cb Expect t3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L226-L237
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L226-L237

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t3d (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .d v = (v .t2 + v .t4) / 2 := by sorry
