-- Prove2me | Theorems.Thm_Csg_cbStageValue_t2
-- name    : Csg.cbStageValue_t2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:15:28.645631+00:00
-- url     : https://prove2.me/theorems/383b3032-2686-4cc4-9c47-e7c930e0ae5c
-- title:
--   Csg: cb Stage Value t2
-- statement:
--   The Csg construction uses the cb Stage Value t2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L335-L384
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L335-L384

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_t2 (v : CBState → ℝ) :
    cbCSG.stageValue .t2 v = min (v .t2) ((v .t1 + v .t3) / 2) := by sorry
