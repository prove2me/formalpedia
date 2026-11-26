-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutSeparatedFailureEnvelope_density_ballot_le
-- name    : FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_density_ballot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:08.075187+00:00
-- url     : https://prove2.me/theorems/1d3e613c-d954-51c0-b7ef-0a7e3f2153c6
-- title:
--   First Passage Linear Transport: timeout Separated Failure Envelope density ballot le
-- statement:
--   Full separated timeout-envelope estimate using the finite ballot timeout
--   profile.  Relative to `timeoutSeparatedFailureEnvelope_density_sharp_le`, the
--   extra reciprocal rank in the landing estimate cancels the linear reverse
--   loss and leaves the critical terminal factor `L⁻¹⁄² exp (-b L)`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L156-L280
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L156-L280

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

theorem FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_density_ballot_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {M L S : ℕ} {H dHi D b₀ b : ℝ}
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
    (hD : 0 ≤ D) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (rStar : ℝ)) *
          (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
            ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) := by sorry
