-- Prove2me | Theorems.Thm_FD1D_inventoryStatePerm_count
-- name    : FD1D.inventoryStatePerm_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:29.895817+00:00
-- url     : https://prove2.me/theorems/fec777d6-46f9-4332-9239-9f7e01461527
-- title:
--   FD1 D: inventory State Perm count
-- statement:
--   The FD1 D construction uses the inventory State Perm count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L85-L88
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L85-L88

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.inventoryStatePerm_count {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 i = x.1 (e.symm i) := by sorry

attribute [defeq] FD1D.inventoryStatePerm_count
