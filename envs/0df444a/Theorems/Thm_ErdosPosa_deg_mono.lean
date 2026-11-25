-- Prove2me | Theorems.Thm_ErdosPosa_deg_mono
-- name    : ErdosPosa.deg_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:26.218142+00:00
-- url     : https://prove2.me/theorems/59f8e56b-e478-5bfc-bb58-234fcc8e1e2f
-- title:
--   Erdos Posa: deg mono
-- statement:
--   The Erdos Posa construction uses the deg mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L41-L42
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L41-L42

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

theorem ErdosPosa.deg_mono [Finite V] {H₁ H : SimpleGraph V} (h : H₁ ≤ H) (v : V) : deg H₁ v ≤ deg H v := by sorry
