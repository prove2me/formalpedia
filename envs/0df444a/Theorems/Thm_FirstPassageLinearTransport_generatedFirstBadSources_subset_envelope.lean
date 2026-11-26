-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_subset_envelope
-- name    : FirstPassageLinearTransport.generatedFirstBadSources_subset_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:56.940525+00:00
-- url     : https://prove2.me/theorems/b4062e61-680c-519b-b0b5-e0f3f0ad4745
-- title:
--   First Passage Linear Transport: generated First Bad Sources subset envelope
-- statement:
--   Every generated finite-chain first-bad witness lies in the direct
--   loss-filtered transport envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L191-L201
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L191-L201

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.generatedFirstBadSources_subset_envelope
    {M L U H : ℕ} {r : ℚ} {t : ℝ} (hr : 0 < r) :
    generatedFirstBadSources M L U H r t ⊆
      firstBadLandingEnvelope M L U H r t := by sorry
