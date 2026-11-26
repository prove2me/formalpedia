-- Prove2me | Theorems.Thm_FD1D_haarCombination_sq_integrable
-- name    : FD1D.haarCombination_sq_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:05.751778+00:00
-- url     : https://prove2.me/theorems/28c6dd6d-da27-51bb-986d-b1456b0e463a
-- title:
--   FD1 D: haar Combination sq integrable
-- statement:
--   The FD1 D construction uses the haar Combination sq integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1722-L1737
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1722-L1737

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.haarCombination_sq_integrable (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    Integrable (fun z => haarCombination l p b z ^ 2) := by sorry
