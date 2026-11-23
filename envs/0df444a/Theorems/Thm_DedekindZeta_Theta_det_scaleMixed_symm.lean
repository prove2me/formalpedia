-- Prove2me | Theorems.Thm_DedekindZeta_Theta_det_scaleMixed_symm
-- name    : DedekindZeta.Theta.det_scaleMixed_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:19:30.334126+00:00
-- url     : https://prove2.me/theorems/dcaa81fb-0502-4261-82d2-de961e4117cc
-- title:
--   Theta: det scale Mixed symm
-- statement:
--   Determinant of the inverse √2-weighting as an `ℝ`-linear endomorphism of the
--   mixed space: it fixes `r₁` real coordinates and scales the `r₂` complex
--   coordinates (real dimension 2 each) by `(√2)⁻¹`, hence has determinant
--   `((√2)⁻¹) ^ (2·r₂)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1926-L1942
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1926-L1942

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open Module

theorem DedekindZeta.Theta.det_scaleMixed_symm :
    LinearMap.det ((scaleMixed K).symm.toLinearEquiv.toLinearMap :
        mixedSpace K →ₗ[ℝ] mixedSpace K)
      = ((Real.sqrt 2)⁻¹) ^ (2 * nrComplexPlaces K) := by sorry
