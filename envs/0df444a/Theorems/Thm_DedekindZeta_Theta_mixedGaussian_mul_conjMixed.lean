-- Prove2me | Theorems.Thm_DedekindZeta_Theta_mixedGaussian_mul_conjMixed
-- name    : DedekindZeta.Theta.mixedGaussian_mul_conjMixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:21:22.061887+00:00
-- url     : https://prove2.me/theorems/0e1e895c-6262-4990-b151-2e5732ca9439
-- title:
--   Theta: mixed Gaussian mul conj Mixed
-- statement:
--   `mixedGaussian` is invariant under conjugating the second factor: since
--   `mixedGaussian` depends only on the per-place Minkowski norms, and
--   `normAtPlace w` is multiplicative (`map_mul`) and `conjMixed`-invariant
--   (`normAtPlace_conjMixed`), we have `g(z · conj ξ) = g(z · ξ)`.  This is what
--   makes the conjugation twist in `dualLattice_idealLattice` disappear from the
--   Gaussian dual sum.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2201-L2211
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2201-L2211

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.mixedGaussian_mul_conjMixed (z ξ : mixedSpace K) :
    mixedGaussian K (z * conjMixed K ξ) = mixedGaussian K (z * ξ) := by sorry
