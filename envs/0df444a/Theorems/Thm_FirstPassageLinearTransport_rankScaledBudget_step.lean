-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rankScaledBudget_step
-- name    : FirstPassageLinearTransport.rankScaledBudget_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:42.112347+00:00
-- url     : https://prove2.me/theorems/2f7d15d7-56b7-5ac6-b090-f04ff97e7408
-- title:
--   First Passage Linear Transport: rank Scaled Budget step
-- statement:
--   One numerical rank step preserves the budget `(q + 2) / r`.  The old
--   threshold has rank `q + d + 1`, so at least one bit of scale is gained.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L55-L82
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L55-L82

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.rankScaledBudget_step
    {q d : ℕ} {r previous newLoss : ℚ}
    (hr : 0 < r)
    (hprevious : previous ≤ ((q + (d + 1) + 2 : ℕ) : ℚ) / r)
    (hlocal : newLoss ≤ ((q + 1 : ℕ) : ℚ) / (2 * r)) :
    (1 / (2 : ℚ) ^ (d + 1)) * previous + newLoss ≤
      ((q + 2 : ℕ) : ℚ) / r := by sorry
