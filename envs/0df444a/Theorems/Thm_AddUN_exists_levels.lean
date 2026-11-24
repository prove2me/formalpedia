-- Prove2me | Theorems.Thm_AddUN_exists_levels
-- name    : AddUN.exists_levels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:18.22977+00:00
-- url     : https://prove2.me/theorems/2898115d-61b5-4d96-86c9-0be7ed528c49
-- title:
--   Add UN: exists levels
-- statement:
--   For a compact set `K` of positive measure there is a sequence `M` of levels with this
--   property. If `M k ≤ h k` for all `k`, then some measurable set of positive measure consists of
--   points `u` such that every point that agrees with `u` outside the range of `h` lies in `K`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L122-L208
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L122-L208

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}

theorem AddUN.exists_levels {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0) :
    ∃ M : ℕ → ℕ, Monotone M ∧ ∀ h : ℕ → ℕ, (∀ k, M k ≤ h k) →
      ∃ Good : Set (ℕ → Bool), MeasurableSet Good ∧ cantorMeasure Good ≠ 0 ∧
        ∀ u ∈ Good, ∀ y : ℕ → Bool, (∀ i, i ∉ range h → y i = u i) → y ∈ K := by sorry
