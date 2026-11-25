-- Prove2me | Theorems.Thm_ErdosPosa_psi_restr_compl
-- name    : ErdosPosa.psi_restr_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:05.719985+00:00
-- url     : https://prove2.me/theorems/96a408ee-8a9a-4ab4-919a-cbf2064c34e0
-- title:
--   Erdos Posa: psi restr compl
-- statement:
--   The Erdos Posa construction uses the psi restr compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L217-L261
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L217-L261

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

theorem ErdosPosa.psi_restr_compl [Fintype V] (hT : MinCyc H₀ T) (hdeg : ∀ v, deg H₀ v ≤ 3) :
    psi H₀ ≤ psi (restr H₀ Tᶜ) + 2 * ({t | t ∈ T ∧ deg H₀ t = 3}.ncard : ℤ) := by sorry
