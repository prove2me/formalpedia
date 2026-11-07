-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_affine
-- name    : AaronsonAmbainis.Bridge.variance_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:23.933219+00:00
-- url     : https://prove2.me/theorems/9a33112e-5a4a-464a-a5e2-9654963f3095
-- title:
--   Bridge: variance affine
-- statement:
--   The Bridge construction uses the variance affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L31-L36
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L31-L36

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.variance_affine (a b : ℝ) (g : Cube ι → ℝ) :
    variance (fun x => a + b * g x) = b ^ 2 * variance g := by sorry
