-- Prove2me | Theorems.Thm_FD1D_haarCombination_integrable
-- name    : FD1D.haarCombination_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:08.275675+00:00
-- url     : https://prove2.me/theorems/a320ac3a-ac2a-44d0-8504-9195cb7c2474
-- title:
--   FD1 D: haar Combination integrable
-- statement:
--   The FD1 D construction uses the haar Combination integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1716-L1720
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1716-L1720

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.haarCombination_integrable (l p b : ι → ℝ) :
    Integrable (haarCombination l p b) := by sorry
