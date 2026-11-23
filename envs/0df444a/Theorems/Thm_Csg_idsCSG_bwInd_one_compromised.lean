-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_one_compromised
-- name    : Csg.idsCSG_bwInd_one_compromised
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:53:57.070967+00:00
-- url     : https://prove2.me/theorems/db6dc171-1703-4e3c-9086-e2dfc1baba22
-- title:
--   Csg: ids CSG bw Ind one compromised
-- statement:
--   Numeric form at `compromised`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L242-L243
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L242-L243

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_one_compromised : idsCSG.bwInd (fun _ => 0) 1 .compromised = 4 / 3 := by sorry
