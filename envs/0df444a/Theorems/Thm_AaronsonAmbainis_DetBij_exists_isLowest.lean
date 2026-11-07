-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_exists_isLowest
-- name    : AaronsonAmbainis.DetBij.exists_isLowest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:36.233201+00:00
-- url     : https://prove2.me/theorems/fd4f3b6e-716a-46e3-9928-ab5467ada8e7
-- title:
--   Det Bij: exists is Lowest
-- statement:
--   A nonzero polynomial has a monomial of least total degree.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L25-L31
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L25-L31

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.exists_isLowest (q : MvPolynomial ι ℤ) (hq : q ≠ 0) : ∃ m, IsLowest q m := by sorry
