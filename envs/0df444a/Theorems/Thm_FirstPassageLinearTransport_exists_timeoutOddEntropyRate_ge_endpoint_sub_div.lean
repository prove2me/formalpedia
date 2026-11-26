-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_timeoutOddEntropyRate_ge_endpoint_sub_div
-- name    : FirstPassageLinearTransport.exists_timeoutOddEntropyRate_ge_endpoint_sub_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:56.292101+00:00
-- url     : https://prove2.me/theorems/bfed4154-7357-5325-97d7-3165a68dd1e1
-- title:
--   First Passage Linear Transport: exists timeout Odd Entropy Rate ge endpoint sub div
-- statement:
--   The exact timeout entropy rate reaches the endpoint rate with an explicit
--   `O(1/L)` loss, uniformly over all parent ranks `m ≥ L`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L692-L765
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L692-L765

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.exists_timeoutOddEntropyRate_ge_endpoint_sub_div
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        firstPassageEndpointRate - D / (L : ℝ) ≤
          timeoutOddEntropyRate K₀ L m := by sorry
