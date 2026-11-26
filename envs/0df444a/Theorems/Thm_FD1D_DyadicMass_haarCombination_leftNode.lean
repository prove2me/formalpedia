-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarCombination_leftNode
-- name    : FD1D.DyadicMass.haarCombination_leftNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:56.282139+00:00
-- url     : https://prove2.me/theorems/b8b69691-b3c6-50f8-a329-d9a37876a8af
-- title:
--   Dyadic Mass: haar Combination left Node
-- statement:
--   The Dyadic Mass construction uses the haar Combination left Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1195-L1204
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1195-L1204

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarCombination_leftNode {L : ℕ} (b : CompleteHaarNode L → ℝ)
    (z : ℝ) :
    (∑ v : CompleteHaarNode L, b v *
      dyadicTent (haarNodeLeft (leftNode v)) (haarNodeWidth (leftNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z) := by sorry
