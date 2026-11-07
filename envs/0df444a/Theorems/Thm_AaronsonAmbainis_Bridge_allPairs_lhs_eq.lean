-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_allPairs_lhs_eq
-- name    : AaronsonAmbainis.Bridge.allPairs_lhs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:14.994804+00:00
-- url     : https://prove2.me/theorems/3b0e8c33-2cf4-4106-91df-f9f79730439b
-- title:
--   Bridge: all Pairs lhs eq
-- statement:
--   The Bridge construction uses the all Pairs lhs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L188-L196
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L188-L196

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.allPairs_lhs_eq (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (w : ι → ℝ) :
    ∑ p ∈ (univ.filter fun x : Cube ι => g x = true) ×ˢ
          (univ.filter fun y : Cube ι => g y = false),
        1 / (∑ j ∈ diffSet p.1 p.2, w j * lam p.1 j * lam p.2 j)
      = ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ := by sorry
