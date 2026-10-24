-- Prove2me | solution 1 for shifted_boxes_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:31:15.70683+00:00
-- url     : https://prove2.me/submissions/39fb8f4f-c6e5-45bd-81a9-c9dcc9292aaa

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    Bornology.IsBounded
      (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
        {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) := by
  classical
  apply (Bornology.isBounded_biUnion
    (s := (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)))
    (strictWeightedSimplex w (T + Finset.univ.sum w)).finite_toSet).2
  intro a ha
  have hpi : Bornology.IsBounded
      (Set.pi Set.univ fun i : Fin n => Set.Icc (a i : Real) ((a i : Real) + 1)) :=
    Bornology.IsBounded.pi fun i => Metric.isBounded_Icc _ _
  apply hpi.subset
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_and]
  intro i _
  exact ⟨(hx i).1, (hx i).2.le⟩