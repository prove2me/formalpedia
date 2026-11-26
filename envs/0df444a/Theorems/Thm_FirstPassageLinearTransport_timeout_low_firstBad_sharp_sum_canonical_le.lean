-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_low_firstBad_sharp_sum_canonical_le
-- name    : FirstPassageLinearTransport.timeout_low_firstBad_sharp_sum_canonical_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:25.4482+00:00
-- url     : https://prove2.me/theorems/c964b816-5157-40e7-a22d-cd26068951c1
-- title:
--   First Passage Linear Transport: timeout low first Bad sharp sum canonical le
-- statement:
--   Canonical form of the sharp timeout sum.  It is intentionally stated
--   with the same series constant as the moving endpoint scalar assembly; the
--   unused dyadic summand only enlarges that constant.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L94-L193
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L94-L193

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.timeout_low_firstBad_sharp_sum_canonical_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 2 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H C b₀ b : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        (C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hC : 0 ≤ C) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ∑ p ∈ Finset.Icc (L + 1) S,
        ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) *
        exactSharpCriticalLowSeriesConstant b₀ C *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by sorry
