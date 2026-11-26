-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rankWeight_nat
-- name    : FirstPassageLinearTransport.rankWeight_nat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:15:44.268656+00:00
-- url     : https://prove2.me/theorems/9e5a0d8f-a991-421d-a3f2-63c29bf2cc2f
-- title:
--   First Passage Linear Transport: rank Weight nat
-- statement:
--   The elementary geometric weight used by the rank-scaled budget.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L22-L32
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L22-L32

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.rankWeight_nat (q d : ℕ) :
    q + (d + 1) + 2 ≤ 2 ^ d * (q + 3) := by sorry
