-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TwoRegimeRankTrace_elapsed_le
-- name    : FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:17:18.183935+00:00
-- url     : https://prove2.me/theorems/6aecb74c-8fe9-4d41-bcce-7fe802e47bc7
-- title:
--   Two Regime Rank Trace: elapsed le
-- statement:
--   The complete two-regime shortcut time is bounded by the two geometric
--   rank budgets.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L180-L190
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L180-L190

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_le
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by sorry
