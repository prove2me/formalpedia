-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedFailureEnvelope_density_ballot_le
-- name    : FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_density_ballot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:17.162134+00:00
-- url     : https://prove2.me/theorems/10126d62-1875-58f9-95b7-40c7e4bc812f
-- title:
--   First Passage Linear Transport: timeout Strengthened Failure Envelope density ballot le
-- statement:
--   Adding the initial multiplicative-maximum event costs exactly `4 / R`
--   on a dyadic shell.  The timeout and height terms therefore remain separate
--   in the formal quantitative interface.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L301-L351
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L301-L351

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_density_ballot_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {M L S : ℕ} {H dHi D b₀ b R : ℝ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 1 ≤ L)
    (hH0 : 0 ≤ H)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (timeoutHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        D / (((p - 1 : ℕ) : ℝ) *
          Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hD : 0 ≤ D) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    (hR : 0 < R) :
    ((timeoutStrengthenedFailureEnvelope P K₀ M L S R).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (rStar : ℝ)) *
          (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
            ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) +
        4 / R := by sorry
