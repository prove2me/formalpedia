-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_even
-- name    : FirstPassageLinearTransport.rawCollatz_of_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:26.197598+00:00
-- url     : https://prove2.me/theorems/0054452b-1a9c-48c2-bb04-385dfe604245
-- title:
--   First Passage Linear Transport: raw Collatz of even
-- statement:
--   The First Passage Linear Transport construction uses the raw Collatz of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L36-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L36-L38

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawCollatz_of_even {n : ℕ} (hn : n % 2 = 0) :
    rawCollatz n = n / 2 := by sorry
