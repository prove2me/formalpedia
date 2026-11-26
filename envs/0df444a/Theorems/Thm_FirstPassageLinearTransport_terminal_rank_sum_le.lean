-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_terminal_rank_sum_le
-- name    : FirstPassageLinearTransport.terminal_rank_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:00.922141+00:00
-- url     : https://prove2.me/theorems/4fd70b84-78df-49c1-b674-ed6e20af4d1a
-- title:
--   First Passage Linear Transport: terminal rank sum le
-- statement:
--   The dyadic boundary tail and entropy tail are both summable after one
--   linear rank loss, retaining arbitrary strict rate margins.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L97-L150
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L97-L150

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.terminal_rank_sum_le
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp b * Real.exp (-(b * (q : ℝ)))) ≤
      weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) := by sorry
