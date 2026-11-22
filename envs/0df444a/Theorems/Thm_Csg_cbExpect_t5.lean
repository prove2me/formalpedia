-- Prove2me | Theorems.Thm_Csg_cbExpect_t5
-- name    : Csg.cbExpect_t5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:14:17.125844+00:00
-- url     : https://prove2.me/theorems/2acbe93f-dc9e-4a9a-b50f-970f21ec5d9b
-- title:
--   Csg: cb Expect t5
-- statement:
--   The Csg construction uses the cb Expect t5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L210-L211
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L210-L211

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t5 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t5 a1 a2 v = v .t4 := by sorry
