-- Prove2me | solution 1 for vcdim_finite_of_fintype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:01.978811+00:00
-- url     : https://prove2.me/submissions/9157ea16-c409-4eb6-b8a4-0542ee715d3e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Theorems.Thm_vcdim_eq_finset_vcdim

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u}
    (hX : Fintype X) (hdec : DecidableEq X) (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) < ⊤ := by
  let := hX
  let := hdec
  rw [vcdim_eq_finset_vcdim (X := X) C]
  exact WithTop.coe_lt_top _
