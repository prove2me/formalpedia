-- Prove2me | Theorems.Thm_DedekindZeta_Theta_tsum_mixedGaussian_submodule
-- name    : DedekindZeta.Theta.tsum_mixedGaussian_submodule
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:21:34.285391+00:00
-- url     : https://prove2.me/theorems/5c526e1e-620d-44ca-8196-78b560177c94
-- title:
--   Theta: tsum mixed Gaussian submodule
-- statement:
--   **Whole-lattice Gaussian sum splits off the `g(0) = 1` term.** Summing the
--   scaled Gaussian over *all* of `J` (including `0`) gives `1` (from `a = 0`) plus
--   the nonzero-element theta kernel `mixedThetaKernel K J y`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2240-L2278
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2240-L2278

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.tsum_mixedGaussian_submodule (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    ∑' a : (J : Submodule (𝓞 K) K), (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)
      = 1 + mixedThetaKernel K J y := by sorry
