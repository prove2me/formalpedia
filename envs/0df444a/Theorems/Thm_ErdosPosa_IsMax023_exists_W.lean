-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_exists_W
-- name    : ErdosPosa.IsMax023.exists_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:37.172187+00:00
-- url     : https://prove2.me/theorems/0751f58a-7400-4305-a46a-03beb0ce9e73
-- title:
--   Is Max023: exists W
-- statement:
--   The Is Max023 construction uses the exists W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L89-L98
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L89-L98

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

theorem ErdosPosa.IsMax023.exists_W (hH : IsMax023 G H) {T : Set V} (hTc : Cyc G T)
    (hT3 : ∀ v ∈ T, deg H v ≠ 3) : ∃ w ∈ T, deg H w = 2 := by sorry
