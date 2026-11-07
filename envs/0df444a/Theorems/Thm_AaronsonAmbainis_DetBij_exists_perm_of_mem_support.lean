-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_exists_perm_of_mem_support
-- name    : AaronsonAmbainis.DetBij.exists_perm_of_mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:59.095486+00:00
-- url     : https://prove2.me/theorems/9a17f1bd-6c5c-44d9-bcb0-2a0f9e137016
-- title:
--   Det Bij: exists perm of mem support
-- statement:
--   Leibniz: every monomial of `det Q'` comes from a permutation all of whose entries are
--   nonzero.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L85-L101
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L85-L101

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.exists_perm_of_mem_support (g : Cube ι → Bool) (A : Cube ι → Finset ι) (m : ι →₀ ℕ)
    (hm : m ∈ (Qmat g A).det.support) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      m = ∑ x : Ones g, agExp (σ x).1 x.1 := by sorry
