-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_centered_of_firstPassage_reverseProduct_half
-- name    : FirstPassageLinearTransport.oddCount_centered_of_firstPassage_reverseProduct_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:34.670242+00:00
-- url     : https://prove2.me/theorems/ece22774-1ce7-4bcd-bf82-fac245103443
-- title:
--   First Passage Linear Transport: odd Count centered of first Passage reverse Product half
-- statement:
--   Taking logarithms in the exact reverse-product identity converts a
--   positive lower bound for the reverse product into a two-sided odd-count
--   estimate.  The constant two accounts for the widths of the source and landing
--   dyadic shells and for `log P ∈ [-log 2,0]`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L27-L112
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L27-L112

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.oddCount_centered_of_firstPassage_reverseProduct_half
    {n k M q : ℕ} {E : ℝ}
    (hn : 0 < n) (hnShell : n ∈ dyadicShell M)
    (hk : 0 < k) (hfp : IsFirstPassage (2 ^ q) n k)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n k)
    (hE : |driftGap * (k : ℝ) -
      (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ E) :
    |(oddCount n k : ℝ) - (k : ℝ) / 2| ≤
      (E + 2) * Real.log 2 / Real.log 3 := by sorry
