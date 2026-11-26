-- Prove2me | solution 1 for crouzeixProductRemainderIntegrand_contourIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:54.167732+00:00
-- url     : https://prove2.me/submissions/3384eda0-763d-47d7-b1f7-96e2f45b52e4

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_continuous_aeval_divByMonic_X_sub_C
import Theorems.Thm_ContourIntegrable_of_continuousOn


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContourIntegrable
      (fun z => star (Polynomial.eval z p) •
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · exact (p.continuous.star.smul
      (continuous_aeval_divByMonic_X_sub_C A p)).continuousOn
