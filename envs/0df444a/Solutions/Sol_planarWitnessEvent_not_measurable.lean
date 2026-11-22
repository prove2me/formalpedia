-- Prove2me | solution 1 for planarWitnessEvent_not_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:51.603453+00:00
-- url     : https://prove2.me/submissions/124f6d71-1f07-4ede-b4cc-54706e614a6a

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (planarWitnessEvent A) := by
  intro hplanar
  apply hA_non
  have hA_ne_univ : A ≠ Set.univ := fun h => hA_non (h ▸ MeasurableSet.univ)
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem A).mp hA_ne_univ
  have hv : Measurable (fun y : ℝ => (a, y)) :=
    Measurable.prod (by exact measurable_const) (by exact measurable_id)
  have hpre : (fun y : ℝ => (a, y)) ⁻¹' planarWitnessEvent A = A := by
    ext y
    simp only [Set.mem_preimage, planarWitnessEvent, Set.mem_ofPred_eq]
    constructor
    · exact fun ⟨hy, _⟩ => hy
    · exact fun hy => ⟨hy, fun hay => ha (hay ▸ hy)⟩
  exact hpre ▸ hv hplanar
