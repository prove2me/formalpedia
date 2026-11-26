-- Prove2me | Theorems.Thm_FD1D_potentialRemainder_nonneg
-- name    : FD1D.potentialRemainder_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:19.183087+00:00
-- url     : https://prove2.me/theorems/b4c3ef4b-721e-4107-8034-a11a4701a584
-- title:
--   FD1 D: potential Remainder nonneg
-- statement:
--   The FD1 D construction uses the potential Remainder nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L125-L137
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L125-L137

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.potentialRemainder_nonneg
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a) (hq : ∀ d v, q d v ≤ 1) :
    0 ≤ potentialRemainder L a N q := by sorry
