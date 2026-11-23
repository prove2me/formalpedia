-- Prove2me | Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_unitSMul
-- name    : DedekindZeta.Theta.idealThetaKernel_unitSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:16:42.11608+00:00
-- url     : https://prove2.me/theorems/d247ebfc-efa3-469a-b066-f0c8d8d29ca5
-- title:
--   Theta: ideal Theta Kernel unit SMul
-- statement:
--   **`𝓞ˣ`-invariance of the theta kernel**: for a unit
--   `u : (𝓞 K)ˣ` acting by `mixedEmbedding.unitSMul`, the kernel of any ideal `𝔞` is
--   unchanged: `idealThetaKernel K 𝔞 (u • x) = idealThetaKernel K 𝔞 x`. Multiplying
--   `x` by the unit `u` reindexes the sum over nonzero `a ∈ 𝔞` by the bijection
--   `a ↦ u·a` of the nonzero elements of `𝔞`, leaving the total unchanged.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1281-L1306
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1281-L1306

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.idealThetaKernel_unitSMul (𝔞 : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 (u • x) = idealThetaKernel K 𝔞 x := by sorry
