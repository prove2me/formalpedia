-- Prove2me | solution 1 for isPolynomialSpectralSet_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:48.396202+00:00
-- url     : https://prove2.me/submissions/80a08ecd-49f8-4f6b-b452-490c2db01d92

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
import Theorems.Thm_isKPolynomialSpectralSet_affine_iff

set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
        ((fun z => a * z + b) '' X) ↔
      IsPolynomialSpectralSet A X :=
  isKPolynomialSpectralSet_affine_iff A 1 X ha b
