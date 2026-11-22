-- Prove2me | Theorems.Thm_Csg_idsGameCSG_compromised_payoff_col
-- name    : Csg.idsGameCSG_compromised_payoff_col
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:36.890076+00:00
-- url     : https://prove2.me/theorems/872a6066-9590-4a52-8fec-f91edf93e6a2
-- title:
--   Csg: ids Game CSG compromised payoff col
-- statement:
--   Symmetric counterpart of `idsGameCSG_compromised_payoff_row` for the column player: fixing the
--       row at `idsUnifP` makes *every* column strategy pay the same constant.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L130-L147
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L130-L147

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_compromised_payoff_col (b : IDSState → Set.Icc (0 : ℝ) 1)
    {q' : AttackAction → ℝ} (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP q' =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by sorry
