-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLossTotal_succ
-- name    : FirstPassageLinearTransport.reverseLossTotal_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:25.559746+00:00
-- url     : https://prove2.me/theorems/09c98bc6-73a8-4c94-82f4-784673988f4b
-- title:
--   First Passage Linear Transport: reverse Loss Total succ
-- statement:
--   The First Passage Linear Transport construction uses the reverse Loss Total succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L51-L54
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L51-L54

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.reverseLossTotal_succ (n h : ℕ) :
    reverseLossTotal n (h + 1) =
      reverseLossTotal n h + reverseLoss n h := by sorry
