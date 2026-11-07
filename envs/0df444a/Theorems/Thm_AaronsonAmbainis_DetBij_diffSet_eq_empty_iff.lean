-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_diffSet_eq_empty_iff
-- name    : AaronsonAmbainis.DetBij.diffSet_eq_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:07.057208+00:00
-- url     : https://prove2.me/theorems/40d104fd-d2f4-4198-8db6-d4ae1d87d724
-- title:
--   Det Bij: diff Set eq empty iff
-- statement:
--   The Det Bij construction uses the diff Set eq empty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L55-L65
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L55-L65

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.diffSet_eq_empty_iff {x w : Cube ι} : diffSet x w = ∅ ↔ x = w := by sorry
