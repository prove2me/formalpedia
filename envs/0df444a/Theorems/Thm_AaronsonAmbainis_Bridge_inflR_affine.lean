-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_inflR_affine
-- name    : AaronsonAmbainis.Bridge.inflR_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:24.649167+00:00
-- url     : https://prove2.me/theorems/1aca020c-1e59-4573-8a2a-609882401f30
-- title:
--   Bridge: infl R affine
-- statement:
--   The Bridge construction uses the infl R affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L38-L43
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L38-L43

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.inflR_affine (a b : ℝ) (g : Cube ι → ℝ) (j : ι) :
    inflR (fun x => a + b * g x) j = b ^ 2 * inflR g j := by sorry
