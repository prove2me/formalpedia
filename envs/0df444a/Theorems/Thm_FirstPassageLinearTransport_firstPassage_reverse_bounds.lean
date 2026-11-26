-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassage_reverse_bounds
-- name    : FirstPassageLinearTransport.firstPassage_reverse_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:49.940479+00:00
-- url     : https://prove2.me/theorems/06883578-0847-56b2-83bc-8deaafa33164
-- title:
--   First Passage Linear Transport: first Passage reverse bounds
-- statement:
--   First-passage reverse bounds in exact rational arithmetic.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L256-L267
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L256-L267

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.firstPassage_reverse_bounds {Y n h : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    (1 - (h : ℚ) / (2 * (Y : ℚ))) * reverseScale n h ≤ (n : ℚ) ∧
      (n : ℚ) ≤ reverseScale n h := by sorry
