-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_abs_sum_sub_unit_le
-- name    : AaronsonAmbainis.Row.abs_sum_sub_unit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:23.44422+00:00
-- url     : https://prove2.me/theorems/fae23166-80fd-476b-841d-d285edad218d
-- title:
--   Row: abs sum sub unit le
-- statement:
--   For every set `R` of coordinates, `|∑_{b ∈ R} (G(0) - G(e_b))| ≤ 2 D²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L93-L116
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L93-L116

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Row.abs_sum_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) (R : Finset β) :
    |∑ b ∈ R, (G (zero β) - G (unit b))| ≤ 2 * (D : ℝ) ^ 2 := by sorry
