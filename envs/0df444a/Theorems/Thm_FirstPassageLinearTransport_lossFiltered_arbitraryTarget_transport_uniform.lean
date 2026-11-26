-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_uniform
-- name    : FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:32.448433+00:00
-- url     : https://prove2.me/theorems/d1619d2d-44be-4fae-aaf2-fa63b70524bb
-- title:
--   First Passage Linear Transport: loss Filtered arbitrary Target transport uniform
-- statement:
--   The uniform form used by the nested re-certification argument.  When the
--   landing threshold lies below the source shell, the additive `1` in the exact
--   transport bound is absorbed by `2^M / Y`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L345-L383
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L345-L383

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_uniform
    {M Y H : ℕ} (B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by sorry
