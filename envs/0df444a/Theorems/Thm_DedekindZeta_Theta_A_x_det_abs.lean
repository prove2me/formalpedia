-- Prove2me | Theorems.Thm_DedekindZeta_Theta_A_x_det_abs
-- name    : DedekindZeta.Theta.A_x_det_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:06.800519+00:00
-- url     : https://prove2.me/theorems/3a5228f8-d56f-4560-8841-d7c94e463a81
-- title:
--   Theta: A x det abs
-- statement:
--   **Determinant of `A_x`.** Conjugation by `toMinkowski` leaves the determinant
--   unchanged, so it equals `|det (mulLeft ℝ x)|` on `mixedSpace K`: over each real
--   place the block is scalar `x_w`, over each complex place multiplication by
--   `x_w ∈ ℂ` as an `ℝ`-linear map has determinant `|x_w|²`, and the product over all
--   places is `∏_w |x_w|^{mult w} = |mixedEmbedding.norm x|`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1517-L1575
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1517-L1575

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.A_x_det_abs {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    |LinearMap.det ((A_x K hx).toLinearEquiv : minkowskiSpace K →ₗ[ℝ] minkowskiSpace K)|
      = |mixedEmbedding.norm x| := by sorry
