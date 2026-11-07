-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_eval_phi
-- name    : AaronsonAmbainis.Row.eval_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:07.808977+00:00
-- url     : https://prove2.me/theorems/0193f16f-1613-445f-a91d-f82a75ba8785
-- title:
--   Row: eval phi
-- statement:
--   The Row construction uses the eval phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L53-L59
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L53-L59

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Row.eval_phi (g : Finset β → ℝ) (R : Finset β) (s : ℝ) :
    (phi g R).eval s = ∑ U : Finset β, g U * ∏ b ∈ U, (if b ∈ R then 1 - s else 1) := by sorry
