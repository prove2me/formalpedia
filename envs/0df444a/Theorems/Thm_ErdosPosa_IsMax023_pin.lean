-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_pin
-- name    : ErdosPosa.IsMax023.pin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:33.200172+00:00
-- url     : https://prove2.me/theorems/522058da-98c6-57bd-bb4b-f1921814e45c
-- title:
--   Is Max023: pin
-- statement:
--   **Pinning lemma.**
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L101-L293
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L101-L293

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}

theorem ErdosPosa.IsMax023.pin (hH : IsMax023 G H) {A : Set V} (hA : ∀ v ∈ A, deg H v ≠ 3) (hc : Cyc G A) :
    ∃ S ⊆ A, Cyc G S ∧ ∃ z ∈ S, ∀ T ⊆ A, MinCyc G T → (∃ x, x ∈ T ∧ x ∈ S) → z ∈ T := by sorry
