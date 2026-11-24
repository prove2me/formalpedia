-- Prove2me | Theorems.Thm_AddUN_exists_between_of_strictMono
-- name    : AddUN.exists_between_of_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:09.793042+00:00
-- url     : https://prove2.me/theorems/0b388416-61a7-43cf-9528-c26b376e5d23
-- title:
--   Add UN: exists between of strict Mono
-- statement:
--   A strictly increasing sequence of natural numbers splits the numbers from its first term on
--   into intervals.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L106-L115
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L106-L115

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

theorem AddUN.exists_between_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) {N i : ℕ} (hi : φ N ≤ i) :
    ∃ n, N ≤ n ∧ φ n ≤ i ∧ i < φ (n + 1) := by sorry
