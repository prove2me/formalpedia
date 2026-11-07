-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_wing_term
-- name    : AaronsonAmbainis.DetBij.wing_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:13.475889+00:00
-- url     : https://prove2.me/theorems/10098554-a845-4d69-9b08-a629d05050b7
-- title:
--   Det Bij: wing term
-- statement:
--   One term of the wing sum, split into the coordinates in `S`, in `A \ S` and outside `A`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L79-L97
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L79-L97

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.wing_term (x z : Cube ι) {A S : Finset ι} (hSA : S ⊆ A) :
    (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i) * ∏ i ∈ A \ S, fAg x z i)
          * ∏ i ∈ Aᶜ, fAg x z i := by sorry
