-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport
-- name    : FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:43.476132+00:00
-- url     : https://prove2.me/theorems/c9ad9c00-7ee8-57e0-b9a1-73329efc6144
-- title:
--   First Passage Linear Transport: loss Filtered arbitrary Target transport
-- statement:
--   Loss-filtered arbitrary-target transport.  The time aggregation costs one
--   factor `H`; the second factor present in the unfiltered theorem is replaced by
--   the sourcewise scaled-loss budget `D`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L285-L340
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L285-L340

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport
    {M Y H : ℕ} (B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
        (B.card : ℚ) := by sorry
