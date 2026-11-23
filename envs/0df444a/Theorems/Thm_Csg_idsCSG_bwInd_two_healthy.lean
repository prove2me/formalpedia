-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_two_healthy
-- name    : Csg.idsCSG_bwInd_two_healthy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:56:21.581649+00:00
-- url     : https://prove2.me/theorems/24368bca-497c-400c-8beb-e183b7f4a212
-- title:
--   Csg: ids CSG bw Ind two healthy
-- statement:
--   Numeric form at `healthy`, matching the real PRISM-games result for round `2`
--       (`1.1904761904762453`) exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L382-L383
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L382-L383

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_two_healthy : idsCSG.bwInd (fun _ => 0) 2 .healthy = 25 / 21 := by sorry
