-- Prove2me | solution 1 for tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:15.488059+00:00
-- url     : https://prove2.me/submissions/ab806b5d-f3cb-4fdb-a49b-a6997209131a

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Theorems.Thm_tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixPolynomialAuxiliaryOperator A Omega p)) := by
  simpa only [crouzeixPolynomialAuxiliaryOperator] using
    tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
      A Omega (fun z ↦ star (Polynomial.eval z p)) q hOmega
        p.continuous.star.continuousOn hCauchy happrox
