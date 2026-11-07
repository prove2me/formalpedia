-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_exists_perm
-- name    : AaronsonAmbainis.DetBij.exists_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:31:14.294407+00:00
-- url     : https://prove2.me/theorems/f146b929-a7ec-4488-8c8b-a78c81d75f29
-- title:
--   Det Bij: exists perm
-- statement:
--   The bijection theorem (Theorem 3.1 of the paper, for the inverse `σ` of the bijection `τ` of
--   the paper), from `LowestUnit` and `LowestBound`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L112-L120
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L112-L120

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.exists_perm (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j := by sorry
