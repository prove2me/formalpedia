-- Prove2me | Theorems.Thm_ErdosPosa_gEP_spec
-- name    : ErdosPosa.gEP_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:00.18815+00:00
-- url     : https://prove2.me/theorems/168d5040-516a-59d4-97f1-dfdf81ebfecd
-- title:
--   Erdos Posa: g EP spec
-- statement:
--   The Erdos Posa construction uses the g EP spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L29-L51
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L29-L51

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
public import Definitions.Def_ErdosPosaLib_EPMain
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.gEP_spec (k : ℕ) :
    (gEP k : ℤ) + 2 * (2 * Nat.log 2 (gEP (k + 1) + 1) + 3) ≤ gEP (k + 1) := by sorry
