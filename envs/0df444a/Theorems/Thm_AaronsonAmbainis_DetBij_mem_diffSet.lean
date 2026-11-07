-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_mem_diffSet
-- name    : AaronsonAmbainis.DetBij.mem_diffSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:56.635278+00:00
-- url     : https://prove2.me/theorems/5f35e653-d282-4d52-a30a-48c6d75e9faa
-- title:
--   Det Bij: mem diff Set
-- statement:
--   The Det Bij construction uses the mem diff Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L24-L25
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L24-L25

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.mem_diffSet {x z : Cube ι} {i : ι} : i ∈ diffSet x z ↔ x i ≠ z i := by sorry
