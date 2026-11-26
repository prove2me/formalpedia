-- Prove2me | solution 1 for exists_polynomial_approximation_scalarCompanionClosedExtension_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:07.868341+00:00
-- url     : https://prove2.me/submissions/8f397360-ee89-4aa2-aad5-6cd5e6c5de7a

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (S : Set ℂ) (hS : S ⊆ closure Omega.carrier) (epsilon : ℕ → ℝ)
    (happrox : ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          epsilon j) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              Omega (a • p) z‖ ≤
          ‖a‖ * epsilon j := by
  obtain ⟨r, hr⟩ := happrox
  refine ⟨fun j => (star a) • r j, ?_⟩
  intro j z hz
  rw [norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
    Omega p (r j) a hkernel (hS hz)]
  exact mul_le_mul_of_nonneg_left (hr j z hz) (norm_nonneg a)
