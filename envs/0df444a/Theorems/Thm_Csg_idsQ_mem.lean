-- Prove2me | Theorems.Thm_Csg_idsQ_mem
-- name    : Csg.idsQ_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:22:50.854463+00:00
-- url     : https://prove2.me/theorems/520fee4d-206b-4adb-98ef-af0abce4a138
-- title:
--   Csg: ids Q mem
-- statement:
--   The Csg construction uses the ids Q mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L176-L177
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L176-L177

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsQ_mem : idsQ ∈ stdSimplex ℝ AttackAction := by sorry
