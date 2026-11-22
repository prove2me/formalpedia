-- Prove2me | solution 1 for exists_measTarget_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:56.967618+00:00
-- url     : https://prove2.me/submissions/a04ba368-5952-4d2a-b736-42a705f43de6

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
public import Theorems.Thm_analytic_nonborel_set_gives_measTarget_separation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  obtain ⟨A, hA_an, hA_non⟩ := hex
  exact analytic_nonborel_set_gives_measTarget_separation A hA_an hA_non
