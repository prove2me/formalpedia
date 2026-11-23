-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_two_compromised
-- name    : Csg.idsCSG_bwInd_two_compromised
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:24.884262+00:00
-- url     : https://prove2.me/theorems/fac4f973-a571-4107-b509-b382dde51cd4
-- title:
--   Csg: ids CSG bw Ind two compromised
-- statement:
--   Numeric form at `compromised`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L386-L387
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L386-L387

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_two_compromised : idsCSG.bwInd (fun _ => 0) 2 .compromised = 46 / 21 := by sorry
