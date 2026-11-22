-- Prove2me | solution 1 for singleton_badEvent_not_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:50.780617+00:00
-- url     : https://prove2.me/submissions/369aff50-0cca-4a86-b7ce-b238a6488df5

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
public import Theorems.Thm_singleton_badEvent_eq_preimage_planar
public import Theorems.Thm_planarWitnessEvent_not_measurable

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (singletonBadEvent A) := by
  intro hbad
  rw [singleton_badEvent_eq_preimage_planar A] at hbad
  have hmeas : Measurable samplePair1ToPlane :=
    Measurable.prod ((measurable_pi_apply 0).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd)
  have hsurj : Function.Surjective samplePair1ToPlane := by
    intro ⟨x, y⟩
    exact ⟨(fun _ => x, fun _ => y), by simp [samplePair1ToPlane]⟩
  have hplanar := (hmeas.measurableSet_preimage_iff_of_surjective hsurj).mp hbad
  exact planarWitnessEvent_not_measurable A hA_non hplanar
