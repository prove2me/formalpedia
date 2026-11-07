-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sum_sub_unit
-- name    : AaronsonAmbainis.Row.sum_sub_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:09.304193+00:00
-- url     : https://prove2.me/theorems/3bb0026e-cae2-4498-b9f3-62e8d9aec9e1
-- title:
--   Row: sum sub unit
-- statement:
--   `∑_{b ∈ R} (G(0) - G(e_b)) = 2 ∑_U g_U |U ∩ R|` for `G = ∑_U g_U chi_U`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L72-L90
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L72-L90

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Row.sum_sub_unit (g : Finset β → ℝ) (R : Finset β) :
    ∑ b ∈ R, ((∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by sorry
