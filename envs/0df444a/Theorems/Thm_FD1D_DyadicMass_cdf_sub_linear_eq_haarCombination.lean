-- Prove2me | Theorems.Thm_FD1D_DyadicMass_cdf_sub_linear_eq_haarCombination
-- name    : FD1D.DyadicMass.cdf_sub_linear_eq_haarCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:31:02.451653+00:00
-- url     : https://prove2.me/theorems/96546659-9cbe-5943-afbe-df9c0075d912
-- title:
--   Dyadic Mass: cdf sub linear eq haar Combination
-- statement:
--   The canonical node sum is the CDF deviation on the unit interval.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1309-L1314
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1309-L1314

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.cdf_sub_linear_eq_haarCombination {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by sorry
