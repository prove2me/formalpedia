-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseProduct_bounds
-- name    : FirstPassageLinearTransport.reverseProduct_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:39.03156+00:00
-- url     : https://prove2.me/theorems/558431e8-5c26-5944-965d-b32e3e5f6e7b
-- title:
--   First Passage Linear Transport: reverse Product bounds
-- statement:
--   The First Passage Linear Transport construction uses the reverse Product bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L214-L245
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L214-L245

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseProduct_bounds {Y n h : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    1 - (h : ℚ) / (2 * (Y : ℚ)) ≤ reverseProduct n h ∧
      reverseProduct n h ≤ 1 := by sorry
