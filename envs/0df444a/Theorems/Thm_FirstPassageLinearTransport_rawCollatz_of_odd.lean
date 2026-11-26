-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_odd
-- name    : FirstPassageLinearTransport.rawCollatz_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:44.205795+00:00
-- url     : https://prove2.me/theorems/b94bfea8-8d20-5142-a60e-ed84279846b5
-- title:
--   First Passage Linear Transport: raw Collatz of odd
-- statement:
--   The First Passage Linear Transport construction uses the raw Collatz of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L40-L42
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L40-L42

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawCollatz_of_odd {n : ℕ} (hn : n % 2 = 1) :
    rawCollatz n = 3 * n + 1 := by sorry
