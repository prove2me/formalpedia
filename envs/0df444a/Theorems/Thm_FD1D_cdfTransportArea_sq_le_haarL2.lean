-- Prove2me | Theorems.Thm_FD1D_cdfTransportArea_sq_le_haarL2
-- name    : FD1D.cdfTransportArea_sq_le_haarL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:12.625826+00:00
-- url     : https://prove2.me/theorems/a5205ced-78b7-5b57-8bf5-6c40009dfd5d
-- title:
--   FD1 D: cdf Transport Area sq le haar L2
-- statement:
--   The FD1 D construction uses the cdf Transport Area sq le haar L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1761-L1772
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1761-L1772

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.cdfTransportArea_sq_le_haarL2 (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    cdfTransportArea (haarCombination l p b) ^ 2 ≤ haarL2 l p b := by sorry
