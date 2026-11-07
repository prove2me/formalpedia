-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_Qmat_apply
-- name    : AaronsonAmbainis.DetBij.Qmat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:52.867216+00:00
-- url     : https://prove2.me/theorems/77f7d296-37e3-4115-a6a9-8a5763926849
-- title:
--   Det Bij: Qmat apply
-- statement:
--   The Det Bij construction uses the Qmat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L39-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L39-L40

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.Qmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x z : Ones g) :
    Qmat g A x z = if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0 := by sorry
