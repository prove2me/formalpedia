-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_exists_lowest_le_bdry
-- name    : AaronsonAmbainis.DetLow.exists_lowest_le_bdry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:15.365204+00:00
-- url     : https://prove2.me/theorems/15e61059-a396-45c6-b490-5e0ee644d03d
-- title:
--   Det Low: exists lowest le bdry
-- statement:
--   The Det Low construction uses the exists lowest le bdry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Corollary.lean#L20-L24
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Corollary.lean#L20-L24

import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Definitions.Def_AaronsonAmbainis_DetLow_Corollary
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.exists_lowest_le_bdry {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) :
    ∃ m : ι →₀ ℕ, IsLowest (agMatrix g).det m ∧ ∀ j, m j ≤ bdry g j := by sorry
