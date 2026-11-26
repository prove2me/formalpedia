-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstBadLandingEnvelope_card_le
-- name    : FirstPassageLinearTransport.firstBadLandingEnvelope_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:51.999605+00:00
-- url     : https://prove2.me/theorems/3c00561f-1f7c-500c-ac15-c35541ffafea
-- title:
--   First Passage Linear Transport: first Bad Landing Envelope card le
-- statement:
--   Exact rank-by-rank transport bound for the first-bad landing envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L126-L164
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L126-L164

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.firstBadLandingEnvelope_card_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by sorry
