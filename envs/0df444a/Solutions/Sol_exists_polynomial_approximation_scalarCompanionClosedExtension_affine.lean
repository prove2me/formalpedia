-- Prove2me | solution 1 for exists_polynomial_approximation_scalarCompanionClosedExtension_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:10.024489+00:00
-- url     : https://prove2.me/submissions/006d1b76-3b48-4f36-8af5-21a38dbc7102

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
import Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_smul

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a b : ℂ)
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
              Omega (a • p + Polynomial.C b) z‖ ≤
          ‖a‖ * epsilon j := by
  have hscaled :=
    exists_polynomial_approximation_scalarCompanionClosedExtension_smul
      Omega p a hkernel S hS epsilon happrox
  exact
    exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
      Omega (a • p) b hkernel S hS (fun j => ‖a‖ * epsilon j) hscaled
