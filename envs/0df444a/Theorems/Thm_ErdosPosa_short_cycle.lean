-- Prove2me | Theorems.Thm_ErdosPosa_short_cycle
-- name    : ErdosPosa.short_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:24:01.356055+00:00
-- url     : https://prove2.me/theorems/e31554b9-ff04-47f4-b02e-5bed9ce7d8ed
-- title:
--   Erdos Posa: short cycle
-- statement:
--   **Short cycle lemma.**
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L208-L314
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L208-L314

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.short_cycle [Finite V] : ∀ (H : SimpleGraph V),
    (∀ v, deg H v = 0 ∨ deg H v = 2 ∨ deg H v = 3) → ∀ m : ℕ, {v | deg H v = 3}.ncard ≤ m →
    (∃ u w, H.Adj u w) →
    ∃ S, Cyc H S ∧ {v | v ∈ S ∧ deg H v = 3}.ncard ≤ 2 * Nat.log 2 m + 3 := by sorry
