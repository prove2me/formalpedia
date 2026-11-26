-- Prove2me | Theorems.Thm_FD1D_weighted_local_sum
-- name    : FD1D.weighted_local_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:48:46.762971+00:00
-- url     : https://prove2.me/theorems/8a80fdec-c129-490f-a61e-afaf1cbd37bb
-- title:
--   FD1 D: weighted local sum
-- statement:
--   The FD1 D construction uses the weighted local sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L394-L406
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L394-L406

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.weighted_local_sum
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f (d + 1) - weightedLevel f d := by sorry
