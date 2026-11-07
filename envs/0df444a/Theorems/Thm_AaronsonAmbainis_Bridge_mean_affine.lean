-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_mean_affine
-- name    : AaronsonAmbainis.Bridge.mean_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:12.817428+00:00
-- url     : https://prove2.me/theorems/ff8e8e51-cf88-46e8-9361-aedd56601767
-- title:
--   Bridge: mean affine
-- statement:
--   The Bridge construction uses the mean affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L24-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L24-L29

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.mean_affine (a b : ℝ) (g : Cube ι → ℝ) :
    mean (fun x => a + b * g x) = a + b * mean g := by sorry
