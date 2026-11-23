-- Prove2me | Theorems.Thm_Csg_idsCSG_payoff_col
-- name    : Csg.idsCSG_payoff_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:22.962808+00:00
-- url     : https://prove2.me/theorems/67ea3b97-fb7c-4b4e-88b3-a559d1d45325
-- title:
--   Csg: ids CSG payoff col
-- statement:
--   Symmetric counterpart of `idsCSG_payoff_row` for the column player.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L198-L209
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L198-L209

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_payoff_col (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff idsP q' = idsV1 s := by sorry
