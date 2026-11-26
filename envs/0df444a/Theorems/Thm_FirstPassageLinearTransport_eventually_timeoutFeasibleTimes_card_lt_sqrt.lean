-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutFeasibleTimes_card_lt_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutFeasibleTimes_card_lt_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:25:57.792004+00:00
-- url     : https://prove2.me/theorems/8a0fd439-1177-5535-a6d9-66a9031605de
-- title:
--   First Passage Linear Transport: eventually timeout Feasible Times card lt sqrt
-- statement:
--   Eventually every fixed-rank timeout time support has
--   `O(sqrt(M log M))` cardinality.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L782-L831
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L782-L831

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutFeasibleTimes_card_lt_sqrt
    (P : TimeoutHighRunData) (K₀ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      ∀ L q : ℕ,
        ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) <
          (timeoutTimeSupportConstant P C + 1) *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
