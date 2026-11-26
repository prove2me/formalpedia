-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_terminal
-- name    : FirstPassageLinearTransport.wordSurvivesFrom_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:18.542818+00:00
-- url     : https://prove2.me/theorems/8f2df404-a149-4b27-9101-f999653e6ad1
-- title:
--   First Passage Linear Transport: word Survives From terminal
-- statement:
--   Survival includes the endpoint after all letters have been read.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L214-L226
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L214-L226

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.wordSurvivesFrom_terminal
    {lo : ℝ} {increment : Bool → ℝ} {r : ℕ} {z : ℝ}
    {v : Fin r → Bool}
    (h : wordSurvivesFrom lo increment r z v) :
    lo ≤ z + wordIncrementSum increment v := by sorry
