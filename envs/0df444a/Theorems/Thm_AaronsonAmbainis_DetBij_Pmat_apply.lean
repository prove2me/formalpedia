-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_Pmat_apply
-- name    : AaronsonAmbainis.DetBij.Pmat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:53.032271+00:00
-- url     : https://prove2.me/theorems/46b06e6e-87e3-4d11-bc1e-60975e6d7155
-- title:
--   Det Bij: Pmat apply
-- statement:
--   The Det Bij construction uses the Pmat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L35-L37
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L35-L37

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.Pmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    Pmat g A x w
      = if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0 := by sorry
