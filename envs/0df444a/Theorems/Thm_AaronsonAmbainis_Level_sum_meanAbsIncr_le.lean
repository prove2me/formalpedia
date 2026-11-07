-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le
-- name    : AaronsonAmbainis.Level.sum_meanAbsIncr_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:04.990542+00:00
-- url     : https://prove2.me/theorems/d1a2b096-9981-426b-b57c-2a5fd6da205d
-- title:
--   Level: sum mean Abs Incr le
-- statement:
--   If `∑_j |f(u) - f(u^j)| ≤ G` at every point `u`, then `L(f) = ∑_j L_j(f) ≤ G`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L174-L182
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L174-L182

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_meanAbsIncr_le (f : Cube ι → ℝ) {G : ℝ}
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) : ∑ j, meanAbsIncr f j ≤ G := by sorry
