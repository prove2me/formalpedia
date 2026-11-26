-- Prove2me | solution 1 for polynomialSupNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:40.320798+00:00
-- url     : https://prove2.me/submissions/b0ed99b0-7b32-4e59-840a-accdde763e71

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
theorem _root_.solution (p : ℂ[X]) (X : Set ℂ) : 0 ≤ polynomialSupNorm p X :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
