-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarCombination_rightNode
-- name    : FD1D.DyadicMass.haarCombination_rightNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:53.571433+00:00
-- url     : https://prove2.me/theorems/29e7a30b-fd10-5718-9fcc-9917105eb01b
-- title:
--   Dyadic Mass: haar Combination right Node
-- statement:
--   The Dyadic Mass construction uses the haar Combination right Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1206-L1215
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1206-L1215

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarCombination_rightNode {L : ℕ} (b : CompleteHaarNode L → ℝ)
    (z : ℝ) :
    (∑ v : CompleteHaarNode L, b v *
      dyadicTent (haarNodeLeft (rightNode v)) (haarNodeWidth (rightNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z - 1) := by sorry
