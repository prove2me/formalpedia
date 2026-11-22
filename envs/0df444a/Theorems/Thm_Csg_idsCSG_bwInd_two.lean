-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_two
-- name    : Csg.idsCSG_bwInd_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:56:57.197806+00:00
-- url     : https://prove2.me/theorems/77041fc7-f50c-4d4f-acc2-c4a7878e5bde
-- title:
--   Csg: ids CSG bw Ind two
-- statement:
--   **The headline result.** Two rounds remaining: `bwInd`'s recursive step applied to `idsV1`
--       (itself the one-round-remaining `bwInd` value, not the raw terminal reward) -- the first place
--       in this project `bwInd`'s recursion is actually exercised, rather than applied once to a
--       literal constant.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L375-L378
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L375-L378

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_two (s : IDSState) : idsCSG.bwInd (fun _ => 0) 2 s = idsV2 s := by sorry
