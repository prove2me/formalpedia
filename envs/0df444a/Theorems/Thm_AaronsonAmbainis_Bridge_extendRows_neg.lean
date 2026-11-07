-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_extendRows_neg
-- name    : AaronsonAmbainis.Bridge.extendRows_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:13.711833+00:00
-- url     : https://prove2.me/theorems/53ac5d82-d026-464a-a3b7-87729328f8a6
-- title:
--   Bridge: extend Rows neg
-- statement:
--   The Bridge construction uses the extend Rows neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L119-L122
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L119-L122

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.extendRows_neg {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} {x : Cube ι}
    (h : ¬ (x ∈ zone g ∨ antipode x ∈ zone g)) : extendRows g lam x = fun _ => 1 := by sorry
