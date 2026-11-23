-- Prove2me | Theorems.Thm_DedekindZeta_Theta_norm_unitSMul
-- name    : DedekindZeta.Theta.norm_unitSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:52:04.676771+00:00
-- url     : https://prove2.me/theorems/a1f4b2a1-6c42-4850-921f-5491731b4b50
-- title:
--   Theta: norm unit SMul
-- statement:
--   **`mixedEmbedding.norm` is `𝓞ˣ`-invariant** (re-export of Mathlib's
--   `norm_unit_smul` for use beside `idealThetaKernel_unitSMul`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1310-L1312
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1310-L1312

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.norm_unitSMul (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by sorry
