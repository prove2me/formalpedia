-- Prove2me | Theorems.Thm_Csg_penniesCSG_bwInd_one
-- name    : Csg.penniesCSG_bwInd_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:25:13.040439+00:00
-- url     : https://prove2.me/theorems/512e4198-160a-40da-9c05-d3c441c2ceb2
-- title:
--   Csg: pennies CSG bw Ind one
-- statement:
--   **The payoff, part three.** One step of backward induction on the whole `CSG`, from zero
--       terminal reward, equals `0` -- the fully-assembled `bwInd`/`CSG`/`MatrixGame` stack agrees
--       with the textbook matching-pennies value, end to end.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L142-L144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L142-L144

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesCSG_bwInd_one : penniesCSG.bwInd (0 : Unit → ℝ) 1 () = 0 := by sorry
