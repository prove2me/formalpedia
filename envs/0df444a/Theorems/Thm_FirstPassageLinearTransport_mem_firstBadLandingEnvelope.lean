-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
-- name    : FirstPassageLinearTransport.mem_firstBadLandingEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:06.390021+00:00
-- url     : https://prove2.me/theorems/465cbee7-8cbd-4276-a58e-ff42713a161d
-- title:
--   First Passage Linear Transport: mem first Bad Landing Envelope
-- statement:
--   The First Passage Linear Transport construction uses the mem first Bad Landing Envelope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L113-L123
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L113-L123

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_firstBadLandingEnvelope
    {M L U H n : ℕ} {r : ℚ} {t : ℝ} :
    n ∈ firstBadLandingEnvelope M L U H r t ↔
      ∃ q : ℕ, L ≤ q ∧ q ≤ U ∧ n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage (2 ^ q) n h ∧
          orbit h n ∈ landingBad q t ∧
          scaledReverseLoss (2 ^ q) n h ≤ ((q + 2 : ℕ) : ℚ) / r := by sorry
