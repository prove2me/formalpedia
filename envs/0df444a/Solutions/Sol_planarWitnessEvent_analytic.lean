-- Prove2me | solution 1 for planarWitnessEvent_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:46.677869+00:00
-- url     : https://prove2.me/submissions/fcb8f088-ece1-4a1f-a2ba-9bb7e6a2a1dd

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
    (A : Set ℝ) (hA : AnalyticSet A) :
    AnalyticSet (planarWitnessEvent A) := by
  have h1 : AnalyticSet (Prod.snd ⁻¹' A : Set (ℝ × ℝ)) :=
    hA.preimage continuous_snd
  have h2 : AnalyticSet ({q : ℝ × ℝ | q.1 ≠ q.2}) := by
    have : MeasurableSet ({q : ℝ × ℝ | q.1 = q.2}) :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    exact this.compl.analyticSet
  have hinter : planarWitnessEvent A = (Prod.snd ⁻¹' A) ∩ {q | q.1 ≠ q.2} := by
    ext q; simp [planarWitnessEvent, and_comm]
  rw [hinter]
  rw [Set.inter_eq_iInter]
  exact AnalyticSet.iInter (fun b => by cases b <;> simpa using by assumption)
