-- Prove2me | Theorems.Thm_AaronsonAmbainis_wing_of_row
-- name    : AaronsonAmbainis.wing_of_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:50.133848+00:00
-- url     : https://prove2.me/theorems/08743e51-c737-42c1-bd4a-5e3250cf2b51
-- title:
--   Aaronson Ambainis: wing of row
-- statement:
--   Steps 1 and 2 of the proof of Lemma 4.2 of the paper: if `x` is a row at `u`, `g u = true`
--   and `S = ∑ j, w j * x j * y j > 0`, then `{j : 1 / w j < S⁻¹ * y j}` is a 1-wing at `u`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L24-L65
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L24-L65

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.wing_of_row {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j)
    (hpos : 0 < ∑ j, w j * x j * y j) :
    IsWing g u (univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j) := by sorry
