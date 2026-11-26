-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutShellBad_subset_collatzSurvivalShell
-- name    : FirstPassageLinearTransport.timeoutShellBad_subset_collatzSurvivalShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:02.25001+00:00
-- url     : https://prove2.me/theorems/e90fe82d-9f6b-49c0-865e-c0b648c2db56
-- title:
--   First Passage Linear Transport: timeout Shell Bad subset collatz Survival Shell
-- statement:
--   Literal low-stage timeout sources are contained in the corresponding
--   uniform finite-word barrier event.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L774-L785
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L774-L785

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutShellBad_subset_collatzSurvivalShell
    {K₀ C : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ))
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    timeoutShellBad K₀ L m ⊆
      collatzSurvivalShell m ((C * K₀ / 2 + 3) * Real.log 2) := by sorry
