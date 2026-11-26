-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_lt_parentMass_of_pos
-- name    : FD1D.V5.LocalPolicy.orderedBias_lt_parentMass_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:04.982666+00:00
-- url     : https://prove2.me/theorems/eb29df17-7145-5d48-8200-81c9638ad40c
-- title:
--   Local Policy: ordered Bias lt parent Mass of pos
-- statement:
--   The Local Policy construction uses the ordered Bias lt parent Mass of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L127-L153
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L127-L153

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.orderedBias_lt_parentMass_of_pos
    {a p h : ℝ} {x y : ℕ}
    (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y) :
    orderedBias a p h x y < parentMass h x y := by sorry
