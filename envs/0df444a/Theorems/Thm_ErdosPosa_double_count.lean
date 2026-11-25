-- Prove2me | Theorems.Thm_ErdosPosa_double_count
-- name    : ErdosPosa.double_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:46.740873+00:00
-- url     : https://prove2.me/theorems/51e54af1-9a5b-5575-88e9-3529396c2ab5
-- title:
--   Erdos Posa: double count
-- statement:
--   The Erdos Posa construction uses the double count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L182-L215
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L182-L215

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
open Classical

theorem ErdosPosa.double_count [Fintype V] :
    ∑ v, (if v ∉ T then ((H₀.neighborSet v ∩ T).ncard : ℤ) else 0) =
      ∑ t, (if t ∈ T then ((H₀.neighborSet t \ T).ncard : ℤ) else 0) := by sorry
