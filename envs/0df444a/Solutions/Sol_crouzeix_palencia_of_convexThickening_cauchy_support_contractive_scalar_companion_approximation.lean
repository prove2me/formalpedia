-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:21.90192+00:00
-- url     : https://prove2.me/submissions/d3313896-eb09-4218-a883-fe79babc233a

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
import Theorems.Thm_polynomialSupNorm_le_add_of_uniform_approximation
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨g, r, hg, happrox, hrlim⟩ := hcompanion p n
  refine ⟨r, ?_, hrlim⟩
  intro j
  exact polynomialSupNorm_le_add_of_uniform_approximation
    (r j) (compactThickeningApprox (closure (numericalRange A)) n) g
    (polynomialSupNorm p
      (compactThickeningApprox (closure (numericalRange A)) n))
    (1 / ((j : ℝ) + 1))
    (polynomialSupNorm_nonneg p
      (compactThickeningApprox (closure (numericalRange A)) n))
    (by positivity) hg (happrox j)
