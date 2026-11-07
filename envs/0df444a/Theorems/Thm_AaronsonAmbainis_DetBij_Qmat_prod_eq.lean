-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_Qmat_prod_eq
-- name    : AaronsonAmbainis.DetBij.Qmat_prod_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:12.889652+00:00
-- url     : https://prove2.me/theorems/9c3369dc-03ec-440e-be79-92b52dc2bf45
-- title:
--   Det Bij: Qmat prod eq
-- statement:
--   A product of entries of `Q'` along a permutation is `0` or a single monomial.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L62-L73
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L62-L73

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.Qmat_prod_eq (g : Cube ι → Bool) (A : Cube ι → Finset ι) (σ : Equiv.Perm (Ones g)) :
    ∏ x : Ones g, Qmat g A (σ x) x
      = if ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
        then monomial (∑ x : Ones g, agExp (σ x).1 x.1) (1 : ℤ) else 0 := by sorry
