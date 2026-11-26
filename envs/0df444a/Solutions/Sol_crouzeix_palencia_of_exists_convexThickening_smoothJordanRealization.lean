-- Prove2me | solution 1 for crouzeix_palencia_of_exists_convexThickening_smoothJordanRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:11.223626+00:00
-- url     : https://prove2.me/submissions/3155bb33-0578-4cb1-8c79-a8a9bf2d8c5a

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_smoothJordanRealization

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hrealize : ∃ Omega : ℕ → SmoothJordanDomain,
      ∀ n, (Omega n).carrier =
        convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  obtain ⟨Omega, hcarrier⟩ := hrealize
  exact crouzeix_palencia_of_convexThickening_smoothJordanRealization
    A Omega hcarrier
