-- Prove2me | Theorems.Thm_Csg_unif3_mem
-- name    : Csg.unif3_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:56:27.430303+00:00
-- url     : https://prove2.me/theorems/8552ef45-c3fe-400e-acc9-60b6bf4b64d0
-- title:
--   Csg: unif3 mem
-- statement:
--   The Csg construction uses the unif3 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L202-L203
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L202-L203

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.unif3_mem : unif3 ∈ stdSimplex ℝ RPSAction := by sorry
