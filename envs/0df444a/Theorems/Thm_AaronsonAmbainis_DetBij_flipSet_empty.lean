-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_empty
-- name    : AaronsonAmbainis.DetBij.flipSet_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:58.22175+00:00
-- url     : https://prove2.me/theorems/574be802-be93-48e1-89ee-fda67bb7ea30
-- title:
--   Det Bij: flip Set empty
-- statement:
--   The Det Bij construction uses the flip Set empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L32-L34
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L32-L34

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetBij.flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by sorry
