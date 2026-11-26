-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:37.204155+00:00
-- url     : https://prove2.me/submissions/2fa71390-4639-4255-8a15-20723bf1fcfa

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_exists_polynomial_rate_approximation_of_tendstoUniformlyOn
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega n).canonicalOrientation p)
          atTop (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
      A Omega K hanti hcompact hnonempty hinter hK hOmega hnest
  intro p n hp hp0
  obtain ⟨q, hq⟩ := happrox p n hp hp0
  exact exists_polynomial_rate_approximation_of_tendstoUniformlyOn
    (K n)
    (crouzeixPolynomialScalarCompanionClosedExtension
      (Omega n).canonicalOrientation p) q hq
