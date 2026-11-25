-- Prove2me | Theorems.Thm_ErdosPosa_deg_restr_compl_of_notMem
-- name    : ErdosPosa.deg_restr_compl_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:39.523748+00:00
-- url     : https://prove2.me/theorems/ed980638-58c6-4518-b7f5-c5405d4dc66f
-- title:
--   Erdos Posa: deg restr compl of not Mem
-- statement:
--   The Erdos Posa construction uses the deg restr compl of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L169-L175
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L169-L175

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}

theorem ErdosPosa.deg_restr_compl_of_notMem {v : V} (hv : v ∉ T) :
    deg (restr H₀ Tᶜ) v = (H₀.neighborSet v \ T).ncard := by sorry
