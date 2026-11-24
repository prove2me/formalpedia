-- Prove2me | Theorems.Thm_AddUN_measure_sUnion_null_of_mk_lt_add
-- name    : AddUN.measure_sUnion_null_of_mk_lt_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:27.558996+00:00
-- url     : https://prove2.me/theorems/8a2c75a1-55eb-4acf-9514-54172df50608
-- title:
--   Add UN: measure s Union null of mk lt add
-- statement:
--   For every finite measure `μ` on the Cantor space, a union of fewer than `add 𝒩` `μ`-null
--   sets is `μ`-null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L71-L75
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L71-L75

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding

theorem AddUN.measure_sUnion_null_of_mk_lt_add (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {𝒢 : Set (Set (ℕ → Bool))} (h𝒢 : ∀ G ∈ 𝒢, μ G = 0) (hcard : #𝒢 < add 𝒩) :
    μ (⋃₀ 𝒢) = 0 := by sorry
