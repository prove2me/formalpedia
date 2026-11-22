-- Prove2me | Theorems.Thm_Csg_cbExpect_t1
-- name    : Csg.cbExpect_t1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:13:57.665223+00:00
-- url     : https://prove2.me/theorems/99aea66d-b244-4028-a3da-df28993e517b
-- title:
--   Csg: cb Expect t1
-- statement:
--   The Csg construction uses the cb Expect t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L198-L199
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L198-L199

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_t1 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t1 a1 a2 v = v .t1 := by sorry
