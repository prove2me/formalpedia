-- Prove2me | Theorems.Thm_Csg_cbStageValue_t4
-- name    : Csg.cbStageValue_t4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:15:24.131554+00:00
-- url     : https://prove2.me/theorems/2ecb1c25-1616-488b-82e1-c2a72faed098
-- title:
--   Csg: cb Stage Value t4
-- statement:
--   The Csg construction uses the cb Stage Value t4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L297-L301
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L297-L301

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_t4 (v : CBState → ℝ) : cbCSG.stageValue .t4 v = v .t5 := by sorry
