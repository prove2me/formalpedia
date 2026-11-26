-- Prove2me | solution 1 for isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:18.076831+00:00
-- url     : https://prove2.me/submissions/ae487585-6184-47fa-b50b-9edf30fa0887

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set
import Theorems.Thm_isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A]
    {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsPolynomialSpectralSet A K :=
  (isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal A).mono_set
    hsub hK
