-- Prove2me | Theorems.Thm_AddUN_exists_clopens_summable
-- name    : AddUN.exists_clopens_summable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:30:02.349527+00:00
-- url     : https://prove2.me/theorems/c47ba8c8-8923-4b43-86a6-f569c2bc413e
-- title:
--   Add UN: exists clopens summable
-- statement:
--   Every null set is covered infinitely often by a sequence of clopen sets whose measures have
--   a finite sum.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L77-L102
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L77-L102

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

theorem AddUN.exists_clopens_summable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {G : Set (ℕ → Bool)} (hG : μ G = 0) :
    ∃ B : ℕ → Clopens (ℕ → Bool), ∑' i, μ (B i) ≠ ∞ ∧
      ∀ x ∈ G, ∃ᶠ i in atTop, x ∈ B i := by sorry
