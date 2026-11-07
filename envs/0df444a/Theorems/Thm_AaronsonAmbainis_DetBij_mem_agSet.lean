-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_mem_agSet
-- name    : AaronsonAmbainis.DetBij.mem_agSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:57.495549+00:00
-- url     : https://prove2.me/theorems/cbceac11-d9f6-4b2b-bc82-f71756b8eb08
-- title:
--   Det Bij: mem ag Set
-- statement:
--   The Det Bij construction uses the mem ag Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L20-L21
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L20-L21

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.mem_agSet {x z : Cube ι} {i : ι} : i ∈ agSet x z ↔ x i = z i := by sorry
