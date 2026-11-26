-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseProduct_succ
-- name    : FirstPassageLinearTransport.reverseProduct_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:23.58648+00:00
-- url     : https://prove2.me/theorems/6d032214-f1cc-5b59-b1c6-01bbde61d784
-- title:
--   First Passage Linear Transport: reverse Product succ
-- statement:
--   The First Passage Linear Transport construction uses the reverse Product succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L63-L66
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L63-L66

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseProduct_succ (n h : ℕ) :
    reverseProduct n (h + 1) =
      reverseProduct n h * reverseStepFactor n h := by sorry
