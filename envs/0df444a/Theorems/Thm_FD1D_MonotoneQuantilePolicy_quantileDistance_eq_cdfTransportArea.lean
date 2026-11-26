-- Prove2me | Theorems.Thm_FD1D_MonotoneQuantilePolicy_quantileDistance_eq_cdfTransportArea
-- name    : FD1D.MonotoneQuantilePolicy.quantileDistance_eq_cdfTransportArea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:47.256891+00:00
-- url     : https://prove2.me/theorems/ef358e34-1428-4c6e-9992-c40a1bbd14d3
-- title:
--   Monotone Quantile Policy: quantile Distance eq cdf Transport Area
-- statement:
--   The Monotone Quantile Policy construction uses the quantile Distance eq cdf Transport Area property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1608-L1613
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1608-L1613

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.MonotoneQuantilePolicy

theorem FD1D.MonotoneQuantilePolicy.quantileDistance_eq_cdfTransportArea {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    P.quantileDistance = cdfTransportArea (fun z => F z - z) := by sorry
