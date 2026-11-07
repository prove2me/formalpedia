-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_derivative_phi_eval_zero
-- name    : AaronsonAmbainis.Row.derivative_phi_eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:15.709034+00:00
-- url     : https://prove2.me/theorems/b9def6cf-0b53-44f8-b94f-5f130f225235
-- title:
--   Row: derivative phi eval zero
-- statement:
--   The Row construction uses the derivative phi eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L61-L69
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L61-L69

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Row.derivative_phi_eval_zero (g : Finset β → ℝ) (R : Finset β) :
    (phi g R).derivative.eval 0 = -∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by sorry
