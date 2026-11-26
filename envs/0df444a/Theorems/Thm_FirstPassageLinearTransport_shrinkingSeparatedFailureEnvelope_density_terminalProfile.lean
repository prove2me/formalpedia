-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingSeparatedFailureEnvelope_density_terminalProfile
-- name    : FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_density_terminalProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:51:07.703257+00:00
-- url     : https://prove2.me/theorems/e69e06b4-74fe-48dc-85cf-121f12dc7169
-- title:
--   First Passage Linear Transport: shrinking Separated Failure Envelope density terminal Profile
-- statement:
--   Conditional master profile.  Its hypotheses are exactly the initial,
--   high-target, low-target, and compressed-time estimates supplied separately
--   by the barrier and schedule modules.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L150-L305
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L150-L305

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_density_terminalProfile
    (P : ShrinkingBarrierRunData)
    {M L S : ℕ} {H dHi bLo bLo' c' : ℝ}
    (hLS : L ≤ S) (hSM : S < M) (hL1 : 1 ≤ L)
    (hH0 : 0 ≤ H)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / P.rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ q ∈ Finset.Icc L S,
      ((landingBad q P.etaLo).card : ℝ) ≤
        1 + (2 : ℝ) ^ q * Real.exp (-(((q - 1 : ℕ) : ℝ) * bLo)))
    (hbLo' : 0 < bLo') (hLoRate : bLo' < bLo)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
        (((M : ℝ) + 1) ^ 2 * dHi + terminalTailBound bLo bLo' c' L) := by sorry
