-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_sum_agExp_apply
-- name    : AaronsonAmbainis.DetBij.sum_agExp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:16.450715+00:00
-- url     : https://prove2.me/theorems/4fc4f0b9-f4da-44d1-aa63-e264b64c7b7e
-- title:
--   Det Bij: sum ag Exp apply
-- statement:
--   The Det Bij construction uses the sum ag Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L103-L108
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L103-L108

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.sum_agExp_apply (g : Cube ι → Bool) (σ : Equiv.Perm (Ones g)) (j : ι) :
    (∑ x : Ones g, agExp (σ x).1 x.1) j
      = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by sorry
