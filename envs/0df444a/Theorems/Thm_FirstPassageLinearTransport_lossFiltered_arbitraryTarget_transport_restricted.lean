-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_restricted
-- name    : FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_restricted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:38:28.245872+00:00
-- url     : https://prove2.me/theorems/b5b0150d-c7df-557c-aeb0-3d49f38f11be
-- title:
--   First Passage Linear Transport: loss Filtered arbitrary Target transport restricted
-- statement:
--   Arbitrary source restriction can only decrease loss-filtered transported
--   mass.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L387-L399
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L387-L399

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_restricted
    {M Y H : ℕ} (B A : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    (((lossFilteredTransportedSources M Y H B D) ∩ A).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by sorry
