-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_collatzSurvivalResidues
-- name    : FirstPassageLinearTransport.card_collatzSurvivalResidues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:27.387801+00:00
-- url     : https://prove2.me/theorems/2fc191b4-4e21-5c39-a12d-afc4c416be21
-- title:
--   First Passage Linear Transport: card collatz Survival Residues
-- statement:
--   The First Passage Linear Transport construction uses the card collatz Survival Residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L379-L388
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L379-L388

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_collatzSurvivalResidues (m : ℕ) (B : ℝ) :
    (collatzSurvivalResidues m B).card =
      (collatzSurvivalWords m B).card := by sorry
