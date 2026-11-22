-- Prove2me | Theorems.Thm_Csg_cbStageValue_t1
-- name    : Csg.cbStageValue_t1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:15:23.903445+00:00
-- url     : https://prove2.me/theorems/967a522c-47fd-413e-8998-e420ba4f17e8
-- title:
--   Csg: cb Stage Value t1
-- statement:
--   The Csg construction uses the cb Stage Value t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L291-L295
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L291-L295

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_t1 (v : CBState → ℝ) : cbCSG.stageValue .t1 v = v .t1 := by sorry
