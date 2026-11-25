-- Prove2me | Theorems.Thm_ErdosPosa_cyc_of_cyc_restr_compl
-- name    : ErdosPosa.cyc_of_cyc_restr_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:02.079958+00:00
-- url     : https://prove2.me/theorems/c2807625-3df3-527d-b78e-f4f138187f4e
-- title:
--   Erdos Posa: cyc of cyc restr compl
-- statement:
--   The Erdos Posa construction uses the cyc of cyc restr compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L263-L268
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L263-L268

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

theorem ErdosPosa.cyc_of_cyc_restr_compl {A : Set V} (h : Cyc (restr H₀ Tᶜ) A) : Cyc H₀ (A \ T) := by sorry
