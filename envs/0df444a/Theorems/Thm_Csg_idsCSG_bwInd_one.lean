-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_one
-- name    : Csg.idsCSG_bwInd_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:47:00.784377+00:00
-- url     : https://prove2.me/theorems/b46cfff3-05f0-4f52-891a-bbf3da377785
-- title:
--   Csg: ids CSG bw Ind one
-- statement:
--   **The headline result.** One round remaining, `bwInd`'s recursive step applied once to the
--       all-zero terminal reward: `idsV1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L232-L234
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L232-L234

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_one (s : IDSState) : idsCSG.bwInd (fun _ => 0) 1 s = idsV1 s := by sorry
