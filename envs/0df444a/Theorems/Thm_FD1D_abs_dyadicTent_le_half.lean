-- Prove2me | Theorems.Thm_FD1D_abs_dyadicTent_le_half
-- name    : FD1D.abs_dyadicTent_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:58.745551+00:00
-- url     : https://prove2.me/theorems/5957bcbe-fd86-5ab7-84ea-faf2f9ecd400
-- title:
--   FD1 D: abs dyadic Tent le half
-- statement:
--   The FD1 D construction uses the abs dyadic Tent le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L653-L668
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L653-L668

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.abs_dyadicTent_le_half (l p z : ℝ) (hp : 0 < p) :
    |dyadicTent l p z| ≤ 1 / 2 := by sorry
