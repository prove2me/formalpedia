-- Prove2me | Theorems.Thm_FD1D_MonotoneQuantilePolicy_expectedDistance_le
-- name    : FD1D.MonotoneQuantilePolicy.expectedDistance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:43.211165+00:00
-- url     : https://prove2.me/theorems/6904540c-30c3-54f1-ab10-da32ea787730
-- title:
--   Monotone Quantile Policy: expected Distance le
-- statement:
--   The Monotone Quantile Policy construction uses the expected Distance le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1639-L1664
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1639-L1664

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.MonotoneQuantilePolicy

theorem FD1D.MonotoneQuantilePolicy.expectedDistance_le {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F)
    : P.expectedDistance ≤ P.withinError +
      cdfTransportArea (fun z => F z - z) := by sorry
