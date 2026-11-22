-- Prove2me | Theorems.Thm_Csg_cbExpect_t3c
-- name    : Csg.cbExpect_t3c
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:14:15.822795+00:00
-- url     : https://prove2.me/theorems/8a23373d-5fbb-498a-8466-8176566e205c
-- title:
--   Csg: cb Expect t3c
-- statement:
--   The Csg construction uses the cb Expect t3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L204-L205
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L204-L205

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t3c (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .c v = v .t3 := by sorry
