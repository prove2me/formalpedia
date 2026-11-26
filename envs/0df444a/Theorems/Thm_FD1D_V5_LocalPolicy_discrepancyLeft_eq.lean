-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_discrepancyLeft_eq
-- name    : FD1D.V5.LocalPolicy.discrepancyLeft_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:24.881932+00:00
-- url     : https://prove2.me/theorems/29bef65b-27d2-554f-a5c2-ecefad0841ab
-- title:
--   Local Policy: discrepancy Left eq
-- statement:
--   The Local Policy construction uses the discrepancy Left eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L165-L169
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L165-L169

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.discrepancyLeft_eq (a p h : ℝ) (x y : ℕ) :
    discrepancyLeft a p h x y =
      (discrepancy a p h x y - bias a p h x y / a) / 2 := by sorry
