-- Prove2me | solution 1 for crouzeixProductMainIntegrand_contourIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:49.985815+00:00
-- url     : https://prove2.me/submissions/f3f9c257-7865-4072-b1e7-4da22a202f2f

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable
      (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
        resolvent A z) Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
    (p.continuous.star.mul p.continuous).continuousOn
