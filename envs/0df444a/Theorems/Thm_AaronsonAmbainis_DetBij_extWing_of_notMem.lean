-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_extWing_of_notMem
-- name    : AaronsonAmbainis.DetBij.extWing_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:31:58.966353+00:00
-- url     : https://prove2.me/theorems/e7db931e-5432-4c48-9294-1d57b066467c
-- title:
--   Det Bij: ext Wing of not Mem
-- statement:
--   The Det Bij construction uses the ext Wing of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L26-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L26-L29

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.extWing_of_notMem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∉ zone g) : extWing g A x = ∅ := by sorry
