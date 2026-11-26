-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_landingBad_subset_insert_shellBad
-- name    : FirstPassageLinearTransport.landingBad_subset_insert_shellBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:50.331153+00:00
-- url     : https://prove2.me/theorems/0a66e06c-e281-4cd0-8feb-1dc59ba53beb
-- title:
--   First Passage Linear Transport: landing Bad subset insert shell Bad
-- statement:
--   Apart from the upper power-of-two endpoint, the landing target lies in
--   the ordinary dyadic shell of rank `q-1`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L41-L59
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L41-L59

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.landingBad_subset_insert_shellBad
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    landingBad q t ⊆ insert (2 ^ q) (shellInitialWindowBad (q - 1) t) := by sorry
