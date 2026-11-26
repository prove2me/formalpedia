-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_timeout_low_firstBad_ballot_sum_canonical_le
-- name    : FirstPassageLinearTransport.exists_timeout_low_firstBad_ballot_sum_canonical_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:14.29557+00:00
-- url     : https://prove2.me/theorems/7dbad2fd-73c1-430a-ae29-a07d25ec7954
-- title:
--   First Passage Linear Transport: exists timeout low first Bad ballot sum canonical le
-- statement:
--   Concrete low-rank first-timeout sum obtained from the literal Collatz
--   ballot estimate.  The one-bit landing-shell shift contributes only the fixed
--   factor `1/2`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L373-L454
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L373-L454

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_timeout_low_firstBad_ballot_sum_canonical_le
    {P : TimeoutHighRunData} {K₀ Cwin : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hK₀ : 0 ≤ K₀) (hCwin : 0 ≤ Cwin)
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 8 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hwindow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((p - 1 : ℕ) : ℝ) ≤ Cwin * (L : ℝ))
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H) :
    ∃ E : ℝ, 0 < E ∧
      ∑ p ∈ Finset.Icc (L + 1) S,
          ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * E *
          ((1 / Real.sqrt L) *
            Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) := by sorry
