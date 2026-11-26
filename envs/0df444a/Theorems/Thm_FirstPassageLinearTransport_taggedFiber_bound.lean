-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_taggedFiber_bound
-- name    : FirstPassageLinearTransport.taggedFiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:07.351677+00:00
-- url     : https://prove2.me/theorems/f78f8494-2904-5711-8805-d65fc13e7e1a
-- title:
--   First Passage Linear Transport: tagged Fiber bound
-- statement:
--   The tagged-fiber estimate as a rational cardinality bound.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L392-L468
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L392-L468

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.taggedFiber_bound {M Y h y : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      1 + 2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by sorry
