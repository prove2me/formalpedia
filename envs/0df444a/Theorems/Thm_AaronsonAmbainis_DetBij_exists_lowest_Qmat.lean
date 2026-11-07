-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_exists_lowest_Qmat
-- name    : AaronsonAmbainis.DetBij.exists_lowest_Qmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:12.76567+00:00
-- url     : https://prove2.me/theorems/2df5a0d9-bb00-465c-854c-aec4b147d547
-- title:
--   Det Bij: exists lowest Qmat
-- statement:
--   `det Q'` has a monomial `m` with `m j ≤ bdry g j` for all `j`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L40-L59
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean#L40-L59

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.exists_lowest_Qmat (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ m : ι →₀ ℕ, m ∈ (Qmat g A).det.support ∧ ∀ j, m j ≤ bdry g j := by sorry
