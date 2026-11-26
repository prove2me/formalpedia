-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarSeries_eq_haarTermSum
-- name    : FD1D.DyadicMass.haarSeries_eq_haarTermSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:37.774245+00:00
-- url     : https://prove2.me/theorems/4d8c4c47-7484-40f1-bc06-b2924359adb0
-- title:
--   Dyadic Mass: haar Series eq haar Term Sum
-- statement:
--   Pointwise finite internal-node expansion on `[0,1]`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L881-L887
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L881-L887

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.DyadicMass.haarSeries_eq_haarTermSum
    {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z = haarTermSum q.haarTerms z := by sorry
