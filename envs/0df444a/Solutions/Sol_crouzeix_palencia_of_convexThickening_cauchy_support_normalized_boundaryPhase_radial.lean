-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:51.012257+00:00
-- url     : https://prove2.me/submissions/d053cfa6-3a2b-4fb3-b15d-fc9a3d5c365b

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel
  · exact hphaseNormalized
  · intro p n _hp
    exact happrox p n
  · intro p n _hp
    exact hPlemelj p n
