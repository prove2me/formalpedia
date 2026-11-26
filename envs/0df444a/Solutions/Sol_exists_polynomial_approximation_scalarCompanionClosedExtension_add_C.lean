-- Prove2me | solution 1 for exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:46.118712+00:00
-- url     : https://prove2.me/submissions/a2ebdbce-cf76-4e20-95f3-023ff040a006

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C

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
              Omega (p + Polynomial.C a) z‖ ≤
          epsilon j := by
  obtain ⟨r, hr⟩ := happrox
  refine ⟨fun j => r j + Polynomial.C (star a), ?_⟩
  intro j z hz
  rw [norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
    Omega p (r j) a
      (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
      hkernel (hS hz)]
  exact hr j z hz
