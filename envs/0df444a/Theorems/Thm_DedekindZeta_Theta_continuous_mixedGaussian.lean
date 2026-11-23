-- Prove2me | Theorems.Thm_DedekindZeta_Theta_continuous_mixedGaussian
-- name    : DedekindZeta.Theta.continuous_mixedGaussian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:13:44.698711+00:00
-- url     : https://prove2.me/theorems/66c34a9e-74b6-4b07-964e-0fe453f40675
-- title:
--   Theta: continuous mixed Gaussian
-- statement:
--   **Continuity of the Minkowski Gaussian** `x ↦ mixedGaussian K x = exp(-π ⟨x,x⟩)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1048-L1052
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1048-L1052

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.continuous_mixedGaussian : Continuous (mixedGaussian K) := by sorry
