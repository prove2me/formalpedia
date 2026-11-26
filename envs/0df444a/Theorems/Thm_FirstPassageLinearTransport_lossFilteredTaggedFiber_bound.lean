-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFilteredTaggedFiber_bound
-- name    : FirstPassageLinearTransport.lossFilteredTaggedFiber_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:55.929679+00:00
-- url     : https://prove2.me/theorems/20d1472a-78dc-5d1c-91ca-66ad73f0db9c
-- title:
--   First Passage Linear Transport: loss Filtered Tagged Fiber bound
-- statement:
--   Cardinality of one loss-filtered tagged fiber.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L155-L243
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L155-L243

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.lossFilteredTaggedFiber_bound
    {M Y h y : ℕ} {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTaggedFiber M Y h y D).card : ℚ) ≤
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by sorry
