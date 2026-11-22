-- Prove2me | Theorems.Thm_Csg_idsQ2_mem
-- name    : Csg.idsQ2_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:23:40.154979+00:00
-- url     : https://prove2.me/theorems/522157a5-e32d-4d85-956a-9d5ae7851922
-- title:
--   Csg: ids Q2 mem
-- statement:
--   The Csg construction uses the ids Q2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L319-L320
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L319-L320

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsQ2_mem : idsQ2 ∈ stdSimplex ℝ AttackAction := by sorry
