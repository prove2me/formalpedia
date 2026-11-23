-- Prove2me | Theorems.Thm_Csg_cbStageValue_t5
-- name    : Csg.cbStageValue_t5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:15:38.449419+00:00
-- url     : https://prove2.me/theorems/5152b171-b4b0-4a9f-ac8a-2cb5b214ab98
-- title:
--   Csg: cb Stage Value t5
-- statement:
--   The Csg construction uses the cb Stage Value t5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L303-L307
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L303-L307

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_t5 (v : CBState → ℝ) : cbCSG.stageValue .t5 v = v .t4 := by sorry
