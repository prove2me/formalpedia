-- Prove2me | Theorems.Thm_DedekindZeta_Theta_norm_toMinkowski_sq
-- name    : DedekindZeta.Theta.norm_toMinkowski_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:13:25.490541+00:00
-- url     : https://prove2.me/theorems/d3e0f0ef-165b-42a0-b248-e4c7a475fe7e
-- title:
--   Theta: norm to Minkowski sq
-- statement:
--   **The Minkowski quadratic form is the squared Minkowski norm** (general
--   point). Factored out of `mixedGaussian_eq`: for every `x : K_ℝ`,
--   `‖toMinkowski K x‖² = ∑_w mult w · normAtPlace w x²`. Used to dominate the
--   lattice Gaussian sum by the convergent theta series `summable_theta`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1005-L1045
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1005-L1045

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.norm_toMinkowski_sq (x : mixedEmbedding.mixedSpace K) :
    ‖toMinkowski K x‖ ^ 2 =
      ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 := by sorry
