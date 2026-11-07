-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_exists_bijection
-- name    : AaronsonAmbainis.DetBij.exists_bijection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:45:50.65695+00:00
-- url     : https://prove2.me/theorems/4f7cd9cb-420d-4126-8cf3-db531983bcfc
-- title:
--   Det Bij: exists bijection
-- statement:
--   The bijection theorem as stated in the paper (Theorem 3.1; `τ` is the inverse of the
--   permutation of `exists_perm`), from the two interface propositions `LowestUnit` and
--   `LowestBound`, which are proved in the directory `DetLow`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Bijection.lean#L23-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Bijection.lean#L23-L52

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Bijection
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.exists_bijection (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ τ : Equiv.Perm (Ones g), (∀ x : Ones g, A x.1 ⊆ diffSet x.1 (τ x).1) ∧
      ∀ j, (univ.filter fun x : Ones g => (τ x).1 j = x.1 j).card ≤ bdry g j := by sorry
