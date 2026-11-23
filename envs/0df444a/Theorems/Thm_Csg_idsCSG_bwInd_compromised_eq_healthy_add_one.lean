-- Prove2me | Theorems.Thm_Csg_idsCSG_bwInd_compromised_eq_healthy_add_one
-- name    : Csg.idsCSG_bwInd_compromised_eq_healthy_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:59.719538+00:00
-- url     : https://prove2.me/theorems/0c02f869-c2e1-4fd5-a901-cec07c10103f
-- title:
--   Csg: ids CSG bw Ind compromised eq healthy add one
-- statement:
--   **For all `n ≥ 1`.** Unfolding `bwInd`'s recursive step once turns the fact above into a
--       statement about `bwInd` itself: `compromised`'s `n`-round value is always exactly `healthy`'s
--       plus `1`, at *every* round from one onward, not just the two rounds hand-checked above. This
--       genuinely needs `n ≥ 1` (equivalently, is stated here as `n + 1`): at `n = 0`, `bwInd`'s base
--       case is the literal terminal reward `fun _ => 0` for both states alike, so the gap is exactly
--       `0`, not `1` -- the asymmetry only enters once the reward table is actually consulted, at the
--       first stage-game evaluation.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L428-L432
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L428-L432

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_bwInd_compromised_eq_healthy_add_one (n : ℕ) :
    idsCSG.bwInd (fun _ => 0) (n + 1) .compromised =
      idsCSG.bwInd (fun _ => 0) (n + 1) .healthy + 1 := by sorry
