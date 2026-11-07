-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sum_abs_sub_unit_le
-- name    : AaronsonAmbainis.Row.sum_abs_sub_unit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:02:46.304204+00:00
-- url     : https://prove2.me/theorems/32cd3776-852f-4e80-95bc-89ac77328122
-- title:
--   Row: sum abs sub unit le
-- statement:
--   The sensitivity lemma (Lemma 6.3 of the paper), given Markov's inequality at an endpoint.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L119-L124
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L119-L124

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Row.sum_abs_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) :
    ∑ b, |G (zero β) - G (unit b)| ≤ 4 * (D : ℝ) ^ 2 := by sorry
