-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TwoRegimeRankTrace_elapsed_add_potential_le
-- name    : FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_add_potential_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:53.659908+00:00
-- url     : https://prove2.me/theorems/0f27b576-3f82-505d-9ecf-ec2cf1d5953d
-- title:
--   Two Regime Rank Trace: elapsed add potential le
-- statement:
--   Potential invariant for the complete two-regime trace.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L135-L176
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L135-L176

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_add_potential_le
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by sorry
