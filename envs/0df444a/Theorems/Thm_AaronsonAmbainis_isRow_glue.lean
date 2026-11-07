-- Prove2me | Theorems.Thm_AaronsonAmbainis_isRow_glue
-- name    : AaronsonAmbainis.isRow_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:33.924266+00:00
-- url     : https://prove2.me/theorems/a29de2f5-027f-4f84-9476-e1c8ec8289f8
-- title:
--   Aaronson Ambainis: is Row glue
-- statement:
--   The restriction of a row to the free coordinates is a row of the restricted function.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L35-L50
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L35-L50

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.isRow_glue {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} (hlam : ∀ x, IsRow g x (lam x))
    (F : Finset ι) (z u : Cube ι) :
    IsRow (fun u => g (glue F z u)) u (fun j => if j ∈ F then lam (glue F z u) j else 0) := by sorry
