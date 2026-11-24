-- Prove2me | Theorems.Thm_AddUN_exists_localising_slalom
-- name    : AddUN.exists_localising_slalom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:30.065725+00:00
-- url     : https://prove2.me/theorems/187b6273-7716-4222-a34c-6c840b52b0f0
-- title:
--   Add UN: exists localising slalom
-- statement:
--   One slalom of width `2 ^ (3 * mu n + n)` localises every member of a family of fewer than
--   `add 𝒩` functions.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L38-L67
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L38-L67

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding

theorem AddUN.exists_localising_slalom {F : Set (ℕ → ℕ)} (hF : #F < add 𝒩) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f ∈ F, ∀ᶠ n in atTop, f n ∈ S n := by sorry
