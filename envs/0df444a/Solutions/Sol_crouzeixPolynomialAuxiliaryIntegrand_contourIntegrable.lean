-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:29.712625+00:00
-- url     : https://prove2.me/submissions/9b753d6c-7207-4499-9dea-1e89291b5485

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable (fun z => star (Polynomial.eval z p) • resolvent A z)
      Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p)) hOmega p.continuous.star.continuousOn
