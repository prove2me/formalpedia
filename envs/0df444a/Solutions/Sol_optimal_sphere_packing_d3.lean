-- Prove2me | solution 1 for optimal_sphere_packing_d3
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:24:53.921567+00:00
-- url     : https://prove2.me/submissions/79808626-3b8d-445e-8212-1e0bbf51cd01

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Set

theorem solution :
    ∀ (centers : Set (EuclideanSpace ℝ (Fin 3))),
      (∀ x ∈ centers, ∀ y ∈ centers, x ≠ y → dist x y ≥ 1) →
      Filter.limsup (fun R : ℝ =>
        (MeasureTheory.volume (centers ∩ Metric.ball 0 R)).toReal /
        (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)).toReal)
      Filter.atTop ≤ Real.pi / (3 * Real.sqrt 2) := by
  intro centers hsep
  have hd : IsDiscrete centers := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro x hx
    refine ⟨Metric.ball x 1, Metric.isOpen_ball, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyc⟩
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      exact (not_lt_of_ge (hsep y hyc x hx hne)) hy
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨by simp, hx⟩
  have hc : centers.Countable := IsLindelof.of_coe.countable_of_isDiscrete hd
  have hz (R : ℝ) : volume (centers ∩ Metric.ball 0 R) = 0 :=
    (hc.mono Set.inter_subset_left).measure_zero volume
  simp only [hz, ENNReal.toReal_zero, zero_div, limsup_const]
  positivity

#print axioms solution
