-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_atTimes
-- name    : FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_atTimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:58.527157+00:00
-- url     : https://prove2.me/theorems/10c9e6ee-a3c3-5e6d-a1ee-92549cfe43d2
-- title:
--   First Passage Linear Transport: loss Filtered arbitrary Target transport at Times
-- statement:
--   Arbitrary-target transport over a finite set of actual time tags.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L54-L100
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L54-L100

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_atTimes
    {M Y : ℕ} (times B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTransportedSourcesAtTimes M Y times B D).card : ℚ) ≤
      (times.card : ℚ) *
        (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) * (B.card : ℚ) := by sorry
