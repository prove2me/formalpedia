-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_atTimes_uniform
-- name    : FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_atTimes_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:12:26.086587+00:00
-- url     : https://prove2.me/theorems/a4aa8df8-708c-5923-a465-37e885118f57
-- title:
--   First Passage Linear Transport: loss Filtered arbitrary Target transport at Times uniform
-- statement:
--   Uniform support-sensitive transport below the source shell.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L103-L140
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L103-L140

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_atTimes_uniform
    {M Y : ℕ} (times B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    ((lossFilteredTransportedSourcesAtTimes M Y times B D).card : ℚ) ≤
      (times.card : ℚ) * (1 + 3 * D) *
        (2 : ℚ) ^ M / (Y : ℚ) * (B.card : ℚ) := by sorry
