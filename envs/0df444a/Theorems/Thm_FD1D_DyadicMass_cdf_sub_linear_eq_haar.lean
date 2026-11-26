-- Prove2me | Theorems.Thm_FD1D_DyadicMass_cdf_sub_linear_eq_haar
-- name    : FD1D.DyadicMass.cdf_sub_linear_eq_haar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:20.051777+00:00
-- url     : https://prove2.me/theorems/d55f627a-4a79-46e5-aec6-a574c02a36a5
-- title:
--   Dyadic Mass: cdf sub linear eq haar
-- statement:
--   Pointwise integrated Haar expansion of the explicit piecewise-linear CDF.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L462-L484
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L462-L484

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.cdf_sub_linear_eq_haar {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z = q.haarSeries z := by sorry
