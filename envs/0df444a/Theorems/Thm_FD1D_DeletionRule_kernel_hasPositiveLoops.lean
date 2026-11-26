-- Prove2me | Theorems.Thm_FD1D_DeletionRule_kernel_hasPositiveLoops
-- name    : FD1D.DeletionRule.kernel_hasPositiveLoops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:36.731357+00:00
-- url     : https://prove2.me/theorems/ea9a4bd2-aa6b-5f2e-9316-16d23726caa5
-- title:
--   Deletion Rule: kernel has Positive Loops
-- statement:
--   The Deletion Rule construction uses the kernel has Positive Loops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L845-L849
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L845-L849

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

theorem FD1D.DeletionRule.kernel_hasPositiveLoops (R : DeletionRule ι m) :
    R.kernel.HasPositiveLoops := by sorry
