-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_det_inequality_of_perm
-- name    : AaronsonAmbainis.DetBij.det_inequality_of_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:07.893731+00:00
-- url     : https://prove2.me/theorems/541b6e36-f17a-4449-9aff-7e17ba8dadd1
-- title:
--   Det Bij: det inequality of perm
-- statement:
--   The weighted inequality for one instance, from a permutation as in `exists_perm`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L44-L106
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L44-L106

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.det_inequality_of_perm (g : Cube ι → Bool) (ℓ : ι → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (A : Cube ι → Finset ι) (d : Cube ι → ℝ)
    (hd : ∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j)
    (σ : Equiv.Perm (Ones g))
    (hσ : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (extWing g A (σ x).1))
    (hcard : ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j) :
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by sorry
