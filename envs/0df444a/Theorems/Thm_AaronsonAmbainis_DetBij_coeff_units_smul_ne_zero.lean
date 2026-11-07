-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_coeff_units_smul_ne_zero
-- name    : AaronsonAmbainis.DetBij.coeff_units_smul_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:13.744444+00:00
-- url     : https://prove2.me/theorems/076ae77e-8c5f-45b7-94d7-d872c23b8ee1
-- title:
--   Det Bij: coeff units smul ne zero
-- statement:
--   A sign does not change whether a coefficient vanishes.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L77-L81
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L77-L81

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.coeff_units_smul_ne_zero (m : ι →₀ ℕ) (u : ℤˣ) (p : MvPolynomial ι ℤ)
    (h : coeff m (u • p) ≠ 0) : coeff m p ≠ 0 := by sorry
