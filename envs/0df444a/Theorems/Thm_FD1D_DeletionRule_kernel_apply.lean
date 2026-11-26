-- Prove2me | Theorems.Thm_FD1D_DeletionRule_kernel_apply
-- name    : FD1D.DeletionRule.kernel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:30.838784+00:00
-- url     : https://prove2.me/theorems/0bea8f22-5522-4066-90ea-2c4423650225
-- title:
--   Deletion Rule: kernel apply
-- statement:
--   The Deletion Rule construction uses the kernel apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L761-L765
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L761-L765

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

theorem FD1D.DeletionRule.kernel_apply (R : DeletionRule ι m) (x y : InventoryState ι m) :
    R.kernel x y =
      ∑ d, ∑ a, if InventoryState.move x d a = y then
        R.prob x d * (1 / Fintype.card ι : ℝ) else 0 := by sorry

attribute [defeq] FD1D.DeletionRule.kernel_apply
