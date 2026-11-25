-- Prove2me | Theorems.Thm_ChromaticReconstruction_two_pow_le_card_treeClass
-- name    : ChromaticReconstruction.two_pow_le_card_treeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:53:30.238801+00:00
-- url     : https://prove2.me/theorems/a80934ab-cb8e-4947-b223-62c1d5d9f42e
-- title:
--   Chromatic Reconstruction: two pow le card tree Class
-- statement:
--   **Lower bound.** There are at least `2 ^ (⌊√k⌋ - 2)` trees on `k ≥ 3` vertices.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingLower.lean#L144-L189
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingLower.lean#L144-L189

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_CountingLower
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.two_pow_le_card_treeClass {k : ℕ} (hk : 3 ≤ k) :
    2 ^ (Nat.sqrt k - 2) ≤ Nat.card (TreeClass k) := by sorry
