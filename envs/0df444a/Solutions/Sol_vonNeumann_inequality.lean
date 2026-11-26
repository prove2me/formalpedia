-- Prove2me | solution 1 for vonNeumann_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:33.627399+00:00
-- url     : https://prove2.me/submissions/d482bfb7-1402-4544-8b86-b36de10999f5

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Theorems.Thm_vonNeumann_inequality_of_exists_unitary_power_dilation
import Theorems.Thm_exists_unitary_power_dilation


set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem _root_.solution (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  exact vonNeumann_inequality_of_exists_unitary_power_dilation T
    (exists_unitary_power_dilation T hT) p
