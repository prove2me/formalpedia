-- Prove2me | Theorems.Thm_Csg_idsGameCSG_compromised_payoff_row
-- name    : Csg.idsGameCSG_compromised_payoff_row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:36.019067+00:00
-- url     : https://prove2.me/theorems/461d0910-be9f-4fad-af55-89355bb0b46a
-- title:
--   Csg: ids Game CSG compromised payoff row
-- statement:
--   Against `idsUnifQ`, *every* row strategy pays exactly `(b healthy + b compromised) / 2` at
--       `compromised`'s stage game against continuation `b` -- `idsUnifQ` equalises the two pure row
--       actions' payoffs (each is `(b healthy + b compromised) / 2`, checked directly by cases), so any
--       weighted average of them is that same constant. Mirrors
--       `RockPaperScissors.lean`'s `rpsCSG_stageGame_initial_payoff_row`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L109-L126
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L109-L126

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_compromised_payoff_row (b : IDSState → Set.Icc (0 : ℝ) 1)
    {p' : PolicyAction → ℝ} (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff p' idsUnifQ =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by sorry
