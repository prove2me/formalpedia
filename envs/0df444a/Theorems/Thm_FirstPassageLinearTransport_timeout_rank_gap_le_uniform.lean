-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_rank_gap_le_uniform
-- name    : FirstPassageLinearTransport.timeout_rank_gap_le_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:19.857035+00:00
-- url     : https://prove2.me/theorems/c3ea4b5f-8a29-41f4-a94b-0a4b84471027
-- title:
--   First Passage Linear Transport: timeout rank gap le uniform
-- statement:
--   On a low-rank window `m ≤ C L`, the timeout target loses at most a
--   fixed real amount of rank.  This is the floor calculation behind the uniform
--   barrier used in the finite ballot estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L159-L182
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L159-L182

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeout_rank_gap_le_uniform
    {K₀ C : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ)) :
    (m : ℝ) - timeoutTargetRank K₀ L m ≤ C * K₀ / 2 + 1 := by sorry
