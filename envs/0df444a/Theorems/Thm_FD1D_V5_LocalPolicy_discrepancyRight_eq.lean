-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_discrepancyRight_eq
-- name    : FD1D.V5.LocalPolicy.discrepancyRight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:46.888152+00:00
-- url     : https://prove2.me/theorems/dea5deeb-c9af-4917-a061-450581f03bda
-- title:
--   Local Policy: discrepancy Right eq
-- statement:
--   The Local Policy construction uses the discrepancy Right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L171-L175
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L171-L175

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.discrepancyRight_eq (a p h : ℝ) (x y : ℕ) :
    discrepancyRight a p h x y =
      (discrepancy a p h x y + bias a p h x y / a) / 2 := by sorry
