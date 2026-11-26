-- Prove2me | Theorems.Thm_FD1D_weightedLevel_zero
-- name    : FD1D.weightedLevel_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:58.265675+00:00
-- url     : https://prove2.me/theorems/b57508ec-a9c2-4c9d-990f-141ca660d2eb
-- title:
--   FD1 D: weighted Level zero
-- statement:
--   The FD1 D construction uses the weighted Level zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L372-L377
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L372-L377

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.weightedLevel_zero (f : ∀ d, DyadicNode d → ℝ) :
    weightedLevel f 0 = f 0 dyadicRoot := by sorry
