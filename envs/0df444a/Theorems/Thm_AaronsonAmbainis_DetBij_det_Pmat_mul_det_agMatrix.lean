-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_det_Pmat_mul_det_agMatrix
-- name    : AaronsonAmbainis.DetBij.det_Pmat_mul_det_agMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:45.454526+00:00
-- url     : https://prove2.me/theorems/415d23fd-9935-4cbf-8695-8013f086899f
-- title:
--   Det Bij: det Pmat mul det ag Matrix
-- statement:
--   `det P * det M = det U * det Q'`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L34-L37
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L34-L37

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.det_Pmat_mul_det_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    (Pmat g A).det * (agMatrix g).det = (Umat g A).det * (Qmat g A).det := by sorry
