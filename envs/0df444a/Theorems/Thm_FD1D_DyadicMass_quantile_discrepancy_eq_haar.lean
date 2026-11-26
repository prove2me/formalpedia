-- Prove2me | Theorems.Thm_FD1D_DyadicMass_quantile_discrepancy_eq_haar
-- name    : FD1D.DyadicMass.quantile_discrepancy_eq_haar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:32:12.817132+00:00
-- url     : https://prove2.me/theorems/ea72d7c6-f725-4772-9819-981f2c3b1619
-- title:
--   Dyadic Mass: quantile discrepancy eq haar
-- statement:
--   For probability leaf masses, the CDF discrepancy used by the quantile
--   policy is exactly the recursively defined integrated Haar series.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1711-L1714
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1711-L1714

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.DyadicMass.quantile_discrepancy_eq_haar {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    q.piecewiseCDF z - z = q.haarSeries z := by sorry
