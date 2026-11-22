-- Prove2me | Theorems.Thm_Csg_idsGameCSG_compromised_stageValue
-- name    : Csg.idsGameCSG_compromised_stageValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:37.786792+00:00
-- url     : https://prove2.me/theorems/52523943-ab02-44a6-a6c9-3bba577dfa37
-- title:
--   Csg: ids Game CSG compromised stage Value
-- statement:
--   **The payoff.** `compromised`'s stage value against *any* continuation `b` is exactly the
--       average of `b`'s two values -- the two payoff lemmas above, fed into `value_unique` the same
--       way `RockPaperScissors.lean`'s `rpsCSG_stageValue_initial` uses `unif3` on both sides.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L152-L171
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L152-L171

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_compromised_stageValue (b : IDSState → Set.Icc (0 : ℝ) 1) :
    idsGameCSG.stageValue .compromised (fun s' => (b s' : ℝ)) =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by sorry
