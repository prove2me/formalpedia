-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_sub_div_le_reverseProduct_of_scaledLoss
-- name    : FirstPassageLinearTransport.one_sub_div_le_reverseProduct_of_scaledLoss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:50.957158+00:00
-- url     : https://prove2.me/theorems/387bc8a9-543e-5645-b0b4-c1144111b598
-- title:
--   First Passage Linear Transport: one sub div le reverse Product of scaled Loss
-- statement:
--   The First Passage Linear Transport construction uses the one sub div le reverse Product of scaled Loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L56-L62
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L56-L62

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.one_sub_div_le_reverseProduct_of_scaledLoss
    {Y n h : ℕ} {D : ℚ} (hn : 0 < n) (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    1 - D / (Y : ℚ) ≤ reverseProduct n h := by sorry
