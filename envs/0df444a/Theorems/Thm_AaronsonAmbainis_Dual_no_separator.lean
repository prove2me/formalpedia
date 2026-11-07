-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_no_separator
-- name    : AaronsonAmbainis.Dual.no_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:04.88372+00:00
-- url     : https://prove2.me/theorems/0cfbc306-f351-47f9-a84a-703063d6fa6b
-- title:
--   Dual: no separator
-- statement:
--   The Dual construction uses the no separator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Core.lean#L41-L123
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Core.lean#L41-L123

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Core
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.no_separator (t : Finset ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hsep : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ≤ K →
        ∑ S, κ S * (∑ i ∈ S, a i - t S) < 0) : False := by sorry
