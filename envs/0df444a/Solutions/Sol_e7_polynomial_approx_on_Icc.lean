-- Prove2me | solution 1 for e7_polynomial_approx_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:44:31.90035+00:00
-- url     : https://prove2.me/submissions/b416bcad-f85d-4d5b-8334-8ac910c82aba

import Mathlib

open MeasureTheory

/-- Weierstrass approximation on `[0,1]`, extracted from Mathlib's density of
polynomial functions in `C(Icc 0 1, ℝ)`. -/
theorem solution (φ : ContinuousMap (Set.Icc (0 : ℝ) 1).Elem ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : (Set.Icc (0 : ℝ) 1).Elem,
      ‖φ x - p.eval x.1‖ ≤ ε := by
  have hcl : (polynomialFunctions (Set.Icc (0 : ℝ) 1)).topologicalClosure = ⊤ :=
    polynomialFunctions_closure_eq_top 0 1
  have hmem : φ ∈ (polynomialFunctions (Set.Icc (0 : ℝ) 1)).topologicalClosure := by
    rw [hcl]
    simp
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  change q ∈ (polynomialFunctions (Set.Icc (0 : ℝ) 1) : Set (C(Set.Icc (0 : ℝ) 1, ℝ))) at hq
  rw [polynomialFunctions_coe] at hq
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, fun x => ?_⟩
  have hcoe : Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p x = p.eval x.1 := by
    simp
  have hle : ‖φ x - Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p x‖ ≤
      dist φ (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p) := by
    rw [dist_eq_norm]
    simpa using ContinuousMap.norm_coe_le_norm
      (φ - Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p) x
  rw [hcoe] at hle
  have hd : dist φ (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p) < ε := hdist
  linarith
