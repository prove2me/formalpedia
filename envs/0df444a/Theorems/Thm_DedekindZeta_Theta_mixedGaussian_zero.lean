-- Prove2me | Theorems.Thm_DedekindZeta_Theta_mixedGaussian_zero
-- name    : DedekindZeta.Theta.mixedGaussian_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:21:24.921724+00:00
-- url     : https://prove2.me/theorems/f51f9699-0d30-469f-b8e3-6d11c6aeaafb
-- title:
--   Theta: mixed Gaussian zero
-- statement:
--   `mixedGaussian` at `0` is `1` (`g(0) = exp 0 = 1`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2181-L2184
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2181-L2184

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.mixedGaussian_zero : mixedGaussian K 0 = 1 := by sorry
