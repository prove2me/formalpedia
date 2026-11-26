-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_twoRegimeClockPotential_nonneg
-- name    : FirstPassageLinearTransport.twoRegimeClockPotential_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:07.84768+00:00
-- url     : https://prove2.me/theorems/41c46165-429b-4c56-a8cb-6402efe5f37e
-- title:
--   First Passage Linear Transport: two Regime Clock Potential nonneg
-- statement:
--   The First Passage Linear Transport construction uses the two Regime Clock Potential nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L27-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L27-L38

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.twoRegimeClockPotential_nonneg
    {rHi rLo : ℝ} (hrHi : rHi < 1) (hrLo : rLo < 1)
    (S q : ℕ) :
    0 ≤ twoRegimeClockPotential rHi rLo S q := by sorry
