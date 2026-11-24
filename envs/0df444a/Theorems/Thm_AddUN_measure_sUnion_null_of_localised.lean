-- Prove2me | Theorems.Thm_AddUN_measure_sUnion_null_of_localised
-- name    : AddUN.measure_sUnion_null_of_localised
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:40.172608+00:00
-- url     : https://prove2.me/theorems/378e368a-b1c0-4621-b1a2-57eb726e6e08
-- title:
--   Add UN: measure s Union null of localised
-- statement:
--   Let `𝒢` be a family of null sets of a finite measure `μ` on the Cantor space. If every family
--   of at most `#𝒢` functions is localised by a slalom of width `h`, then the union of `𝒢` is
--   `μ`-null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L157-L197
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L157-L197

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN

theorem AddUN.measure_sUnion_null_of_localised (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (h : ℕ → ℕ)
    {𝒢 : Set (Set (ℕ → Bool))} (h𝒢 : ∀ G ∈ 𝒢, μ G = 0)
    (hloc : ∀ F : Set (ℕ → ℕ), #F ≤ #𝒢 → ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) ∧
      ∀ f ∈ F, ∀ᶠ n in atTop, f n ∈ S n) :
    μ (⋃₀ 𝒢) = 0 := by sorry
