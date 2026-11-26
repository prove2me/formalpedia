-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_rate_root
-- name    : FD1D.V5.TreePolicy.rate_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:15.647931+00:00
-- url     : https://prove2.me/theorems/9410296b-dadd-4f85-bed3-69c8052386c1
-- title:
--   Tree Policy: rate root
-- statement:
--   The Tree Policy construction uses the rate root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L68-L70
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L68-L70

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.rate_root (I : AggregatedInventory L m) (a : ℝ) :
    rate I a 0 dyadicRoot = 1 / (m : ℝ) := by sorry

attribute [defeq] FD1D.V5.TreePolicy.rate_root
