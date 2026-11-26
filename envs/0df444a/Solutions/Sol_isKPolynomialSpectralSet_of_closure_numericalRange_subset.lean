-- Prove2me | solution 1 for isKPolynomialSpectralSet_of_closure_numericalRange_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:27.561165+00:00
-- url     : https://prove2.me/submissions/e6a2b217-f0b4-418e-90d5-28dc3e220e98

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set
import Theorems.Thm_crouzeix_palencia


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) K :=
  (crouzeix_palencia A).mono_set (by positivity) hsub hK
