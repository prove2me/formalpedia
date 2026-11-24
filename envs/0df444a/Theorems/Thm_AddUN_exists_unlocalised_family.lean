-- Prove2me | Theorems.Thm_AddUN_exists_unlocalised_family
-- name    : AddUN.exists_unlocalised_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:09.417788+00:00
-- url     : https://prove2.me/theorems/2047c9f6-fb39-40de-85c2-c35731eade1f
-- title:
--   Add UN: exists unlocalised family
-- statement:
--   **Lemma 1.** For every `h : ℕ → ℕ` there is a family `F` of at most `add 𝒩` functions such
--   that no slalom of width `h` localises every member of `F`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L201-L210
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L201-L210

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

theorem AddUN.exists_unlocalised_family (h : ℕ → ℕ) :
    ∃ F : Set (ℕ → ℕ), #F ≤ add 𝒩 ∧
      ∀ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) → ∃ f ∈ F, ∃ᶠ n in atTop, f n ∉ S n := by sorry
