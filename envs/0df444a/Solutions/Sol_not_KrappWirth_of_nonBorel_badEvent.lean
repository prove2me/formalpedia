-- Prove2me | solution 1 for not_KrappWirth_of_nonBorel_badEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:39.303391+00:00
-- url     : https://prove2.me/submissions/9d9665e0-fc64-4193-9996-21218fed4bae

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ)
    (hC : C.Nonempty)
    (hbad : ¬ MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      oneSidedGhostGap h c m p ≥ ε / 2}) :
    ¬ KrappWirthWellBehaved X C := by
  intro hKW
  apply hbad
  have hV := hKW.V_measurable c m
  rw [wellBehaved_event_eq_preimage_gapSup C c m ε hC]
  exact hV measurableSet_Ici
