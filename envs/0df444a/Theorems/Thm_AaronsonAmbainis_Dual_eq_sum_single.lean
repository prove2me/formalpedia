-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_eq_sum_single
-- name    : AaronsonAmbainis.Dual.eq_sum_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:58.427375+00:00
-- url     : https://prove2.me/theorems/de9fc971-0e19-437d-94af-a69cfeb4c0b1
-- title:
--   Dual: eq sum single
-- statement:
--   Every vector is the sum of its coordinates times the unit vectors.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Functional.lean#L22-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Functional.lean#L22-L29

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Functional
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem AaronsonAmbainis.Dual.eq_sum_single (v : β → ℝ) : v = ∑ b, v b • (Pi.single b (1 : ℝ) : β → ℝ) := by sorry
