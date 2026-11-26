-- Prove2me | Theorems.Thm_FD1D_dyadicTent_stronglyMeasurable
-- name    : FD1D.dyadicTent_stronglyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:04.047798+00:00
-- url     : https://prove2.me/theorems/c39e1bb2-4573-4374-ab44-2a9aa98da4ba
-- title:
--   FD1 D: dyadic Tent strongly Measurable
-- statement:
--   The FD1 D construction uses the dyadic Tent strongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L638-L643
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L638-L643

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_stronglyMeasurable (l p : ℝ) :
    StronglyMeasurable (dyadicTent l p) := by sorry
