-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_collatzSurvivalShell
-- name    : FirstPassageLinearTransport.card_collatzSurvivalShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:30.906501+00:00
-- url     : https://prove2.me/theorems/46e21aa0-c3a4-5c1d-a84e-0ecd244f4327
-- title:
--   First Passage Linear Transport: card collatz Survival Shell
-- statement:
--   Exact parity coding identifies shell survivors with abstract word
--   survivors.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L398-L412
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L398-L412

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_collatzSurvivalShell (m : ℕ) (B : ℝ) :
    (collatzSurvivalShell m B).card =
      (collatzSurvivalWords m B).card := by sorry
