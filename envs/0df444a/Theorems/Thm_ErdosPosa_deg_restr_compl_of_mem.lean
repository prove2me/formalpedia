-- Prove2me | Theorems.Thm_ErdosPosa_deg_restr_compl_of_mem
-- name    : ErdosPosa.deg_restr_compl_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:34.685774+00:00
-- url     : https://prove2.me/theorems/ac5e1a42-6361-4a3b-90ef-8e0e648d20de
-- title:
--   Erdos Posa: deg restr compl of mem
-- statement:
--   The Erdos Posa construction uses the deg restr compl of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L163-L167
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L163-L167

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

theorem ErdosPosa.deg_restr_compl_of_mem {v : V} (hv : v ∈ T) : deg (restr H₀ Tᶜ) v = 0 := by sorry
