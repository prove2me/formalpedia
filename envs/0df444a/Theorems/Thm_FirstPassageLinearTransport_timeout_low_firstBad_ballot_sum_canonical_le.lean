-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_low_firstBad_ballot_sum_canonical_le
-- name    : FirstPassageLinearTransport.timeout_low_firstBad_ballot_sum_canonical_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:02.300092+00:00
-- url     : https://prove2.me/theorems/b9c20137-1e32-5a3b-8eb4-7a5e689e24a0
-- title:
--   First Passage Linear Transport: timeout low first Bad ballot sum canonical le
-- statement:
--   Summing the literal ballot timeout profile through the first-bad
--   transport cancels the linear reverse loss and leaves the terminal factor
--   `L⁻¹⁄² exp (-bL)`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L288-L368
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L288-L368

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.timeout_low_firstBad_ballot_sum_canonical_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 1 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H D b₀ b : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        D / (((p - 1 : ℕ) : ℝ) *
          Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hD : 0 ≤ D) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ∑ p ∈ Finset.Icc (L + 1) S,
        ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) *
        (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
          ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) := by sorry
