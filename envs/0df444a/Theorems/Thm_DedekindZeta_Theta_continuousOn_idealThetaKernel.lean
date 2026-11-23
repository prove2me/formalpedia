-- Prove2me | Theorems.Thm_DedekindZeta_Theta_continuousOn_idealThetaKernel
-- name    : DedekindZeta.Theta.continuousOn_idealThetaKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:16.853256+00:00
-- url     : https://prove2.me/theorems/73d4ea80-5436-4af6-adb7-e8e452954da4
-- title:
--   Theta: continuous On ideal Theta Kernel
-- statement:
--   **Continuity of the integral theta kernel** `x ↦ idealThetaKernel K 𝔞 x`,
--   on the nonzero-norm locus, the integral-ideal specialisation of
--   `continuousOn_mixedThetaKernel` via `idealThetaKernel_eq_mixed`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1171-L1178
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1171-L1178

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.continuousOn_idealThetaKernel (𝔞 : Ideal (𝓞 K)) :
    ContinuousOn (idealThetaKernel K 𝔞)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by sorry
