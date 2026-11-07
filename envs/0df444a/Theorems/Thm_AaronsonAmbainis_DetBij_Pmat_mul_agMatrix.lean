-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_Pmat_mul_agMatrix
-- name    : AaronsonAmbainis.DetBij.Pmat_mul_agMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:18.297395+00:00
-- url     : https://prove2.me/theorems/a34b1360-2b05-4f66-82fc-a8a3560c6c9b
-- title:
--   Det Bij: Pmat mul ag Matrix
-- statement:
--   `P * M = U * Q'` (Lemma 3.8 (i) of the paper), using the wing property.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L132-L165
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L132-L165

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.Pmat_mul_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    Pmat g A * agMatrix g = Umat g A * Qmat g A := by sorry
