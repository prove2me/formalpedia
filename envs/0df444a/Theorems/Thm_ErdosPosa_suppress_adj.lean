-- Prove2me | Theorems.Thm_ErdosPosa_suppress_adj
-- name    : ErdosPosa.suppress_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:08.751798+00:00
-- url     : https://prove2.me/theorems/12e284b2-4ea1-5169-a23f-a45889fda3f7
-- title:
--   Erdos Posa: suppress adj
-- statement:
--   The Erdos Posa construction uses the suppress adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L31-L44
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L31-L44

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

theorem ErdosPosa.suppress_adj {H : SimpleGraph V} {x a b u w : V} :
    (suppress H x a b).Adj u w ↔
      (H.Adj u w ∧ u ≠ x ∧ w ≠ x) ∨ (u = a ∧ w = b ∧ a ≠ b) ∨ (u = b ∧ w = a ∧ a ≠ b) := by sorry
