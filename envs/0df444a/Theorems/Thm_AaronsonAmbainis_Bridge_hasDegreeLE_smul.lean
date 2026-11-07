-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:01:58.105755+00:00
-- url     : https://prove2.me/theorems/61c489ed-b0b5-4d45-8d13-2138df34124b
-- title:
--   Bridge: has Degree LE smul
-- statement:
--   The Bridge construction uses the has Degree LE smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L31-L38
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L31-L38

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_smul (r : ℝ) {f : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d) :
    HasDegreeLE (fun x => r * f x) d := by sorry
