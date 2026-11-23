-- Prove2me | Theorems.Thm_Csg_idsP2_mem
-- name    : Csg.idsP2_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:35.074044+00:00
-- url     : https://prove2.me/theorems/0a39ca8c-f6b4-4f04-b592-2bab8d637f70
-- title:
--   Csg: ids P2 mem
-- statement:
--   The Csg construction uses the ids P2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L310-L311
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L310-L311

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsP2_mem : idsP2 ∈ stdSimplex ℝ PolicyAction := by sorry
