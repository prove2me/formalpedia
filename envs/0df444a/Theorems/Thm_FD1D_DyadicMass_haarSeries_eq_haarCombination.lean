-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarSeries_eq_haarCombination
-- name    : FD1D.DyadicMass.haarSeries_eq_haarCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:44.941565+00:00
-- url     : https://prove2.me/theorems/f75d24d7-091b-4084-b873-f9b28764ddc7
-- title:
--   Dyadic Mass: haar Series eq haar Combination
-- statement:
--   The recursive Haar series is exactly the canonical finite sum over all
--   internal nodes `⟨d,k⟩` of the complete depth-`L` tree.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1273-L1306
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1273-L1306

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarSeries_eq_haarCombination {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by sorry
