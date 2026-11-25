-- Prove2me | Theorems.Thm_ErdosPosa_deg_split
-- name    : ErdosPosa.deg_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:58.541797+00:00
-- url     : https://prove2.me/theorems/aece232b-6a1e-4298-9722-d4813525db6a
-- title:
--   Erdos Posa: deg split
-- statement:
--   The Erdos Posa construction uses the deg split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L177-L179
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L177-L179

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

theorem ErdosPosa.deg_split [Finite V] (v : V) :
    deg H₀ v = (H₀.neighborSet v ∩ T).ncard + (H₀.neighborSet v \ T).ncard := by sorry
