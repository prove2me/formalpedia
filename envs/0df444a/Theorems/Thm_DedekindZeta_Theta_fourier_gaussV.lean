-- Prove2me | Theorems.Thm_DedekindZeta_Theta_fourier_gaussV
-- name    : DedekindZeta.Theta.fourier_gaussV
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:17:01.507992+00:00
-- url     : https://prove2.me/theorems/fc6ec957-d0dd-406a-ad85-6033d4d5ca2a
-- title:
--   Theta: fourier gauss V
-- statement:
--   **Fourier self-duality of the Minkowski Gaussian** (the `t = 1` self-dual
--   Gaussian): with respect to the Minkowski inner product on `minkowskiSpace K`,
--   the Fourier transform of `gaussV` is `gaussV`. This is
--   `fourier_gaussian_innerProductSpace` at `b = π`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1408-L1413
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1408-L1413

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.fourier_gaussV (w : minkowskiSpace K) : 𝓕 (gaussV K) w = gaussV K w := by sorry
