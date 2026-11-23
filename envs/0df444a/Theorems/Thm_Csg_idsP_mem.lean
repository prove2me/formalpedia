-- Prove2me | Theorems.Thm_Csg_idsP_mem
-- name    : Csg.idsP_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:21:27.088073+00:00
-- url     : https://prove2.me/theorems/00e40ea9-bdb3-4c98-9b84-7653fc38b7de
-- title:
--   Csg: ids P mem
-- statement:
--   The Csg construction uses the ids P mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L166-L167
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L166-L167

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsP_mem : idsP ∈ stdSimplex ℝ PolicyAction := by sorry
