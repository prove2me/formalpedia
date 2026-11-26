-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_arbitraryTarget_linear_transport
-- name    : FirstPassageLinearTransport.arbitraryTarget_linear_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:20.686078+00:00
-- url     : https://prove2.me/theorems/1d303991-cac4-4fa2-83df-0a139f524eb5
-- title:
--   First Passage Linear Transport: arbitrary Target linear transport
-- statement:
--   Arbitrary-target linear transport.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L135-L186
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L135-L186

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.arbitraryTarget_linear_transport {M Y H : ℕ} (B : Finset ℕ)
    (hY : 0 < Y) (_hH : 1 ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((transportedSources M Y H B).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) ^ 2 * (2 : ℚ) ^ M /
        (Y : ℚ) * (B.card : ℚ) := by sorry
