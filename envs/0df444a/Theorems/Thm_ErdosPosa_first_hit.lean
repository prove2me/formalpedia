-- Prove2me | Theorems.Thm_ErdosPosa_first_hit
-- name    : ErdosPosa.first_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:48.715037+00:00
-- url     : https://prove2.me/theorems/7129ca32-95c9-5628-9bd4-813a6ab12720
-- title:
--   Erdos Posa: first hit
-- statement:
--   The Erdos Posa construction uses the first hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L28-L59
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L28-L59

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

theorem ErdosPosa.first_hit {G' : SimpleGraph V} (P : V → Prop) {x w : V} (p : G'.Walk x w) (hw : P w) :
    ∃ w', P w' ∧ ∃ q : G'.Walk x w', (∀ y ∈ q.support, y ≠ w' → ¬ P y) ∧
      (∀ y ∈ q.support, y ∈ p.support) := by sorry
