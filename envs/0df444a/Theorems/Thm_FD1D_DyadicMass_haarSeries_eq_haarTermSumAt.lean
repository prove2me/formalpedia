-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarSeries_eq_haarTermSumAt
-- name    : FD1D.DyadicMass.haarSeries_eq_haarTermSumAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:20.550949+00:00
-- url     : https://prove2.me/theorems/2f0e6c82-09f7-4e04-bd0b-707e9834f4da
-- title:
--   Dyadic Mass: haar Series eq haar Term Sum At
-- statement:
--   The recursive integrated Haar series is the sum of every internal-node
--   coefficient times its geometric tent, on any positive ambient interval.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L823-L878
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L823-L878

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.DyadicMass.haarSeries_eq_haarTermSumAt
    {L : ℕ} (q : DyadicMass L) {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    q.haarSeries ((z - a) / p) =
      haarTermSum (q.haarTermsAt a p) z := by sorry
