-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_neg_X_mul_gAg_add_fAg
-- name    : AaronsonAmbainis.DetBij.neg_X_mul_gAg_add_fAg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:52.961939+00:00
-- url     : https://prove2.me/theorems/1fd54d70-5eef-40db-b968-1e36b45957e0
-- title:
--   Det Bij: neg X mul g Ag add f Ag
-- statement:
--   A coordinate of the wing contributes `0` if `x_i = z_i` and `1 - s_i^2` otherwise.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L72-L76
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L72-L76

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.neg_X_mul_gAg_add_fAg (x z : Cube ι) (i : ι) :
    -(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i
      = if x i = z i then 0 else 1 - (X i : MvPolynomial ι ℤ) ^ 2 := by sorry
