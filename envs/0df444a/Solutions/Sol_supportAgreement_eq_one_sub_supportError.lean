-- Prove2me | solution 1 for supportAgreement_eq_one_sub_supportError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:24.783932+00:00
-- url     : https://prove2.me/submissions/21c5f2c5-0607-400b-aa4a-f64a05f75691

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution {X : Type u} (Y : Finset X)
    (q : FinitePMF ↥Y) (h c : X → Bool) :
    (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0)) =
    1 - supportError Y q h c := by
  simp only [supportError]
  have : ∀ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0) +
      q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1) = q.prob y := by
    intro y; split_ifs <;> ring
  have hsum : (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0)) +
    (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1)) =
    ∑ y : ↥Y, q.prob y := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun y _ => this y)
  rw [show ∑ y : ↥Y, q.prob y = 1 from q.prob_sum_one] at hsum
  linarith
