-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassage_final_even
-- name    : FirstPassageLinearTransport.firstPassage_final_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:21.11011+00:00
-- url     : https://prove2.me/theorems/3b976956-c245-52f8-9463-e2bd6f746b8d
-- title:
--   First Passage Linear Transport: first Passage final even
-- statement:
--   The final crossing cannot be an odd shortcut step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L25-L34
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L25-L34

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.firstPassage_final_even {Y n k : ℕ}
    (hfp : IsFirstPassage Y n (k + 1)) :
    orbit k n % 2 = 0 := by sorry
