-- Prove2me | solution 1 for uniformMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:50.908615+00:00
-- url     : https://prove2.me/submissions/d56a7762-ed32-4406-9960-130bbf6f4e72

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X] [Fintype X]
    (hne : Nonempty X) (hpos : 0 < Fintype.card X) :
    MeasureTheory.IsProbabilityMeasure (uniformMeasure X hne) := by
  constructor
  unfold uniformMeasure
  change (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count (Set.univ : Set X) = 1
  rw [MeasureTheory.Measure.count_apply_finite' Set.finite_univ MeasurableSet.univ,
      Set.Finite.toFinset_eq_toFinset, Set.toFinset_univ, Finset.card_univ, smul_eq_mul]
  have hne_zero : (Fintype.card X : ENNReal) ≠ 0 := by
    simp [Nat.pos_iff_ne_zero.mp hpos]
  exact ENNReal.div_mul_cancel hne_zero (ENNReal.natCast_ne_top _)
