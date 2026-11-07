-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_prod
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:11.783615+00:00
-- url     : https://prove2.me/theorems/ccf6a5c3-515f-4562-b086-1aa73b33c8b5
-- title:
--   Bridge: has Degree LE prod
-- statement:
--   The Bridge construction uses the has Degree LE prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L110-L122
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L110-L122

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_prod {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {k : α → ℕ}
    (h : ∀ a ∈ s, HasDegreeLE (F a) (k a)) :
    HasDegreeLE (fun x => ∏ a ∈ s, F a x) (∑ a ∈ s, k a) := by sorry
