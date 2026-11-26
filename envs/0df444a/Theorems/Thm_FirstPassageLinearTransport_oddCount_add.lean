-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_add
-- name    : FirstPassageLinearTransport.oddCount_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:25:56.591792+00:00
-- url     : https://prove2.me/theorems/886b8dd4-0b0a-5115-b0b7-4f6289915414
-- title:
--   First Passage Linear Transport: odd Count add
-- statement:
--   Odd counts split exactly under concatenation of shortcut segments.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L92-L99
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L92-L99

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.oddCount_add (n k j : ℕ) :
    oddCount n (k + j) = oddCount n k + oddCount (orbit k n) j := by sorry
