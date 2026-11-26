-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reciprocal_sqrt_entropy_tail_exact_rate_Icc_le
-- name    : FirstPassageLinearTransport.reciprocal_sqrt_entropy_tail_exact_rate_Icc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:24.550618+00:00
-- url     : https://prove2.me/theorems/363401fd-5dcb-4a77-b3eb-a32febf64552
-- title:
--   First Passage Linear Transport: reciprocal sqrt entropy tail exact rate Icc le
-- statement:
--   Exact-rate summation for the reciprocal square-root profile produced when
--   the ballot timeout density cancels the linear reverse-loss factor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L197-L283
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L197-L283

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.reciprocal_sqrt_entropy_tail_exact_rate_Icc_le
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    {L U : ℕ} (hL : 1 ≤ L) (hLU : L + 1 ≤ U) :
    ∑ p ∈ Finset.Icc (L + 1) U,
        ((p + 1 : ℕ) : ℝ) /
            (((p - 1 : ℕ) : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) ≤
      (3 / Real.sqrt L) * Real.exp (-(b * (L : ℝ))) *
        weightedTailConstant b₀ (b₀ / 2) := by sorry
