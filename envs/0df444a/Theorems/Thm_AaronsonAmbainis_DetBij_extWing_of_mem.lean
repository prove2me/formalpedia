-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_extWing_of_mem
-- name    : AaronsonAmbainis.DetBij.extWing_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:31:54.931715+00:00
-- url     : https://prove2.me/theorems/d01a33c6-d485-4a8c-a18d-af112d304680
-- title:
--   Det Bij: ext Wing of mem
-- statement:
--   The Det Bij construction uses the ext Wing of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L21-L24
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L21-L24

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.extWing_of_mem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∈ zone g) : extWing g A x = A x := by sorry
