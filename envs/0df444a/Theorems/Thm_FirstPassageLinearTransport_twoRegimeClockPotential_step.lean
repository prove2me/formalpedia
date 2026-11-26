-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_twoRegimeClockPotential_step
-- name    : FirstPassageLinearTransport.twoRegimeClockPotential_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:17:39.406459+00:00
-- url     : https://prove2.me/theorems/7e917ad7-5b17-4f99-9cf6-15e975036b55
-- title:
--   First Passage Linear Transport: two Regime Clock Potential step
-- statement:
--   One rank step decreases the clock potential by at least the local time.
--   The active contraction is selected by the parent rank `m`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L42-L118
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean#L42-L118

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.twoRegimeClockPotential_step
    {rHi rLo : ℝ} {S qPrev m h q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (hmPrev : m ≤ qPrev) (hhm : h ≤ m)
    (hcontract :
      if S ≤ m then (q : ℝ) ≤ rHi * (m : ℝ)
      else (q : ℝ) ≤ rLo * (m : ℝ)) :
    (h : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      twoRegimeClockPotential rHi rLo S qPrev := by sorry
