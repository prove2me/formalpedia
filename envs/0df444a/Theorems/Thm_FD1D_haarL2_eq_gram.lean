-- Prove2me | Theorems.Thm_FD1D_haarL2_eq_gram
-- name    : FD1D.haarL2_eq_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:46.076065+00:00
-- url     : https://prove2.me/theorems/36ee4219-da56-4903-a690-aae96c543635
-- title:
--   FD1 D: haar L2 eq gram
-- statement:
--   The FD1 D construction uses the haar L2 eq gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1322-L1348
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1322-L1348

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.haarL2_eq_gram (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    haarL2 l p b =
      ∑ i, ∑ j, (b i * b j) *
        ∫ z, dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z := by sorry
