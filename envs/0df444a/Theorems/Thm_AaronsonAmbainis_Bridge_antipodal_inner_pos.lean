-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_antipodal_inner_pos
-- name    : AaronsonAmbainis.Bridge.antipodal_inner_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:29:20.631414+00:00
-- url     : https://prove2.me/theorems/dee1deb9-09d4-4f0e-b0f1-1fa5752b7940
-- title:
--   Bridge: antipodal inner pos
-- statement:
--   No junk value in `AntipodalInequality`: on the zone the inner sum is positive.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L64-L74
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L64-L74

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.antipodal_inner_pos {g : Cube ι → Bool} {u : Cube ι} (hu : u ∈ zone g) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g u (lam u)) (h2 : IsRow g (antipode u) (lam (antipode u))) :
    0 < ∑ j, w j * lam u j * lam (antipode u) j := by sorry
