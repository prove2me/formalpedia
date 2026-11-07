-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_sum
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:48.02279+00:00
-- url     : https://prove2.me/theorems/0c4c79af-7fd2-4a67-b43d-f7f8eb448c40
-- title:
--   Bridge: has Degree LE sum
-- statement:
--   The Bridge construction uses the has Degree LE sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L40-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L40-L53

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_sum {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {d : ℕ}
    (h : ∀ k ∈ s, HasDegreeLE (F k) d) : HasDegreeLE (fun x => ∑ k ∈ s, F k x) d := by sorry
