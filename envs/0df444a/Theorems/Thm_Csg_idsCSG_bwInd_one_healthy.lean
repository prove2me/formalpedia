-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_one_healthy
-- name    : Csg.idsCSG_bwInd_one_healthy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:53:52.937042+00:00
-- url     : https://prove2.me/theorems/6b8e9fb4-7bf2-4522-8483-f3cb40d9b7bf
-- title:
--   Csg: ids CSG bw Ind one healthy
-- statement:
--   Numeric form at `healthy`, matching the real PRISM-games result for round `1`
--       (`0.3333333333333333`) exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L238-L239
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L238-L239

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_one_healthy : idsCSG.bwInd (fun _ => 0) 1 .healthy = 1 / 3 := by sorry
