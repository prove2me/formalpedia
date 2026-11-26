-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_card_timeoutShellBad_endpointRate_le
-- name    : FirstPassageLinearTransport.exists_card_timeoutShellBad_endpointRate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:49.275844+00:00
-- url     : https://prove2.me/theorems/2aabfa7e-6c6c-5196-ba56-d7072e12e7e2
-- title:
--   First Passage Linear Transport: exists card timeout Shell Bad endpoint Rate le
-- statement:
--   Referee-facing sharp timeout density with the endpoint rate and its
--   explicit `D/L` loss.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L1031-L1059
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L1031-L1059

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.exists_card_timeoutShellBad_endpointRate_le
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) *
              (firstPassageEndpointRate - D / (L : ℝ)))) := by sorry
