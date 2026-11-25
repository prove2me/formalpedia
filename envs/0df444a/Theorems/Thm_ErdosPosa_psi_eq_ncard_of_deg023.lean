-- Prove2me | Theorems.Thm_ErdosPosa_psi_eq_ncard_of_deg023
-- name    : ErdosPosa.psi_eq_ncard_of_deg023
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:35.981071+00:00
-- url     : https://prove2.me/theorems/ecbe8f4d-1d10-41fd-a1e6-370cdf6d3be2
-- title:
--   Erdos Posa: psi eq ncard of deg023
-- statement:
--   The Erdos Posa construction uses the psi eq ncard of deg023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L53-L60
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L53-L60

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

theorem ErdosPosa.psi_eq_ncard_of_deg023 [Fintype V] {H : SimpleGraph V} (hH : Deg023 H) :
    psi H = ({v | deg H v = 3}.ncard : ℤ) := by sorry
