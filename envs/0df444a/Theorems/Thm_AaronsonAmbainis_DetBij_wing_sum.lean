-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_wing_sum
-- name    : AaronsonAmbainis.DetBij.wing_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:01.853873+00:00
-- url     : https://prove2.me/theorems/63f4208a-adc2-45ae-9432-dab918493bc5
-- title:
--   Det Bij: wing sum
-- statement:
--   The wing identity (Lemma 3.7 of the paper), for an arbitrary set `A` and points `x`, `z`
--   of the cube.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L101-L127
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L101-L127

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.wing_sum (x z : Cube ι) (A : Finset ι) :
    ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = (∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x z) A then agMon x z else 0) := by sorry
