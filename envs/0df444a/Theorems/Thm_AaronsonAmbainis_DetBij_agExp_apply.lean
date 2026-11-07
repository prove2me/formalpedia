-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_agExp_apply
-- name    : AaronsonAmbainis.DetBij.agExp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:16.785515+00:00
-- url     : https://prove2.me/theorems/be72b984-45f8-4cc6-b70b-ee497d3a918b
-- title:
--   Det Bij: ag Exp apply
-- statement:
--   The Det Bij construction uses the ag Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L84-L92
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L84-L92

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.agExp_apply (x z : Cube ι) (j : ι) : agExp x z j = if x j = z j then 1 else 0 := by sorry
