-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_sub_reverseLossTotal_le_reverseProduct
-- name    : FirstPassageLinearTransport.one_sub_reverseLossTotal_le_reverseProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:40.340066+00:00
-- url     : https://prove2.me/theorems/b3da0696-ba2f-5d87-9cf0-06f0557c64ef
-- title:
--   First Passage Linear Transport: one sub reverse Loss Total le reverse Product
-- statement:
--   The First Passage Linear Transport construction uses the one sub reverse Loss Total le reverse Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L40-L46
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L40-L46

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.one_sub_reverseLossTotal_le_reverseProduct
    {n : ℕ} (hn : 0 < n) (h : ℕ) :
    1 - reverseLossTotal n h ≤ reverseProduct n h := by sorry
