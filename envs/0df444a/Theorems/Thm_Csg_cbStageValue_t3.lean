-- Prove2me | Theorems.Thm_Csg_cbStageValue_t3
-- name    : Csg.cbStageValue_t3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:16:12.443751+00:00
-- url     : https://prove2.me/theorems/630da021-b8e6-4109-b23d-9ec91f21eb8a
-- title:
--   Csg: cb Stage Value t3
-- statement:
--   The Csg construction uses the cb Stage Value t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L412-L461
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L412-L461

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_t3 (v : CBState → ℝ) :
    cbCSG.stageValue .t3 v = max (v .t3) ((v .t2 + v .t4) / 2) := by sorry
