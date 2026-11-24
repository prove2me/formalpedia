-- Prove2me | Theorems.Thm_AddUN_exists_clopens_limsup
-- name    : AddUN.exists_clopens_limsup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:24:27.482829+00:00
-- url     : https://prove2.me/theorems/c8be76f8-9c8a-4970-80f0-35ef7283a5ff
-- title:
--   Add UN: exists clopens limsup
-- statement:
--   Step 1 of Lemma 1. Every null set is contained in the `limsup` of a sequence of clopen sets
--   `C n` with `μ (C n) ≤ ε n`, for every finite measure `μ` on the Cantor space.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L119-L142
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L119-L142

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

theorem AddUN.exists_clopens_limsup (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {G : Set (ℕ → Bool)} (hG : μ G = 0) {ε : ℕ → ℝ≥0∞}
    (hε : ∀ n, ε n ≠ 0) :
    ∃ C : ℕ → Clopens (ℕ → Bool), (∀ n, μ (C n) ≤ ε n) ∧
      ∀ x ∈ G, ∃ᶠ n in atTop, x ∈ C n := by sorry
