-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parentRank_le_rationalTargetBudget
-- name    : FirstPassageLinearTransport.parentRank_le_rationalTargetBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:33.675214+00:00
-- url     : https://prove2.me/theorems/b7104c5b-003d-46da-bd2d-82bf20dca44c
-- title:
--   First Passage Linear Transport: parent Rank le rational Target Budget
-- statement:
--   The floor target supplies the parent-rank inequality required by the
--   rank-scaled loss induction.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L31-L40
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L31-L40

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.parentRank_le_rationalTargetBudget
    {r : ℚ} (hr : 0 < r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / r := by sorry
