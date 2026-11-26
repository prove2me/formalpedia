-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarCombination_eq_zero_of_outside
-- name    : FD1D.DyadicMass.haarCombination_eq_zero_of_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:44.066921+00:00
-- url     : https://prove2.me/theorems/45d961f4-d648-450d-85fe-1f05141abcd3
-- title:
--   Dyadic Mass: haar Combination eq zero of outside
-- statement:
--   The Dyadic Mass construction uses the haar Combination eq zero of outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1231-L1243
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1231-L1243

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarCombination_eq_zero_of_outside {L : ℕ}
    (b : CompleteHaarNode L → ℝ) {z : ℝ} (hz : z ≤ 0 ∨ 1 ≤ z) :
    haarCombination haarNodeLeft haarNodeWidth b z = 0 := by sorry
