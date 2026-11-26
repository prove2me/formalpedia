-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLossTotal_le_div_of_scaled_le
-- name    : FirstPassageLinearTransport.reverseLossTotal_le_div_of_scaled_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:41.347703+00:00
-- url     : https://prove2.me/theorems/e68dc5b4-3300-4585-a984-b405aa273c48
-- title:
--   First Passage Linear Transport: reverse Loss Total le div of scaled le
-- statement:
--   The First Passage Linear Transport construction uses the reverse Loss Total le div of scaled le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L48-L54
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L48-L54

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.reverseLossTotal_le_div_of_scaled_le
    {Y n h : ℕ} {D : ℚ} (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    reverseLossTotal n h ≤ D / (Y : ℚ) := by sorry
