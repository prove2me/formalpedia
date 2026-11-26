-- Prove2me | Theorems.Thm_FD1D_DeletionRule_one_div_card_le_kernel_self
-- name    : FD1D.DeletionRule.one_div_card_le_kernel_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:46.891666+00:00
-- url     : https://prove2.me/theorems/935c0473-fa80-49f6-94b0-404870732983
-- title:
--   Deletion Rule: one div card le kernel self
-- statement:
--   The self-loop probability is at least the uniform arrival mass.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L813-L843
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L813-L843

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

theorem FD1D.DeletionRule.one_div_card_le_kernel_self (R : DeletionRule ι m)
    (x : InventoryState ι m) :
    (1 / Fintype.card ι : ℝ) ≤ R.kernel x x := by sorry
