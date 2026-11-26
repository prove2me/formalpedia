-- Prove2me | Theorems.Thm_FD1D_inventoryStatePerm_image_count
-- name    : FD1D.inventoryStatePerm_image_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:14.649452+00:00
-- url     : https://prove2.me/theorems/a487d194-fc77-408b-ac6c-ad5b2b4e9e40
-- title:
--   FD1 D: inventory State Perm image count
-- statement:
--   The FD1 D construction uses the inventory State Perm image count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L91-L94
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L91-L94

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.inventoryStatePerm_image_count {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 (e i) = x.1 i := by sorry
