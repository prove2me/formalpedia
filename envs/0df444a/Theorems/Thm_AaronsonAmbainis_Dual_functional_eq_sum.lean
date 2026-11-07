-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_functional_eq_sum
-- name    : AaronsonAmbainis.Dual.functional_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:41.814248+00:00
-- url     : https://prove2.me/theorems/0c4203cb-8be1-412a-ad50-af7873b31e2e
-- title:
--   Dual: functional eq sum
-- statement:
--   The Dual construction uses the functional eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Functional.lean#L31-L36
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Functional.lean#L31-L36

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Functional
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Dual.functional_eq_sum (φ : (β → ℝ) →L[ℝ] ℝ) (v : β → ℝ) :
    φ v = ∑ b, φ (Pi.single b 1) * v b := by sorry
