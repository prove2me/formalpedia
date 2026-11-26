-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_taggedFiber_algebra
-- name    : FirstPassageLinearTransport.taggedFiber_algebra
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:59.65677+00:00
-- url     : https://prove2.me/theorems/c238a44d-aa51-529a-9278-87d9f21f61ae
-- title:
--   First Passage Linear Transport: tagged Fiber algebra
-- statement:
--   The First Passage Linear Transport construction uses the tagged Fiber algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L373-L389
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L373-L389

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.taggedFiber_algebra {M Y h : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((h : ℚ) / (2 * (Y : ℚ))) *
          ((2 : ℚ) ^ (M + 1) /
            (1 - (h : ℚ) / (2 * (Y : ℚ)))) =
      2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by sorry
