-- Prove2me | Theorems.Thm_FD1D_DyadicMass_quantile_cost_within_leaf
-- name    : FD1D.DyadicMass.quantile_cost_within_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:32:03.076964+00:00
-- url     : https://prove2.me/theorems/df0cff76-983c-5250-a6c0-3486dd23e809
-- title:
--   Dyadic Mass: quantile cost within leaf
-- statement:
--   The actual selected-leaf endpoint has cost at most the exact quantile cost
--   plus one depth-`L` cell width.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1701-L1705
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1701-L1705

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.DyadicMass.quantile_cost_within_leaf {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    (q.quantilePolicy hq).expectedDistance ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea (fun z => q.piecewiseCDF z - z) := by sorry
