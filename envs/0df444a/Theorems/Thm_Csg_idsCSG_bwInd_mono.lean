-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_mono
-- name    : Csg.idsCSG_bwInd_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:57:13.790908+00:00
-- url     : https://prove2.me/theorems/bb9075d9-91ae-470f-b6f1-fc0963534290
-- title:
--   Csg: ids CSG bw Ind mono
-- statement:
--   **`bwInd`'s sequence is nondecreasing in the round count, at every state.** Reward accumulates
--       without discounting here, and every entry of `idsR` is nonnegative, so one more round of play
--       never lowers the value -- a genuine induction on `n`, unlike the fact above, leaning on
--       `CsgMonotone.lean`'s `stageValue_mono`. Notably, `stageValue_mono` needs no `hr : C.r ≡ 0`
--       hypothesis -- monotonicity in the continuation never depended on the reward-free assumption
--       every previous worked instance in this project happened to satisfy, only boundedness did.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L440-L449
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L440-L449

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_mono (n : ℕ) (s : IDSState) :
    idsCSG.bwInd (fun _ => 0) n s ≤ idsCSG.bwInd (fun _ => 0) (n + 1) s := by sorry
