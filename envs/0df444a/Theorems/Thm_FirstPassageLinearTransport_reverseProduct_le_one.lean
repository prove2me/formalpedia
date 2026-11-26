-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseProduct_le_one
-- name    : FirstPassageLinearTransport.reverseProduct_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:22.325679+00:00
-- url     : https://prove2.me/theorems/2aae58ce-6414-53b6-be07-4fe8f4553ba4
-- title:
--   First Passage Linear Transport: reverse Product le one
-- statement:
--   The First Passage Linear Transport construction uses the reverse Product le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L31-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L31-L38

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.reverseProduct_le_one {n : ℕ} (hn : 0 < n) (h : ℕ) :
    reverseProduct n h ≤ 1 := by sorry
