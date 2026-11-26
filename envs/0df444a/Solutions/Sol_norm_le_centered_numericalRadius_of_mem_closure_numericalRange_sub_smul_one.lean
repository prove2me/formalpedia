-- Prove2me | solution 1 for norm_le_centered_numericalRadius_of_mem_closure_numericalRange_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:47.651196+00:00
-- url     : https://prove2.me/submissions/9286ff58-4cab-400e-97f6-c669af515f66

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_norm_le_numericalRadius_of_mem_closure_numericalRange

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange (A - c • (1 : E →L[ℂ] E)))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_numericalRadius_of_mem_closure_numericalRange
    (A - c • (1 : E →L[ℂ] E)) hz
