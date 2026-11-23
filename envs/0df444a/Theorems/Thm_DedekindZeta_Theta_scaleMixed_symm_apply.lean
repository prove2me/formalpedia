-- Prove2me | Theorems.Thm_DedekindZeta_Theta_scaleMixed_symm_apply
-- name    : DedekindZeta.Theta.scaleMixed_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:23.677793+00:00
-- url     : https://prove2.me/theorems/026fd9f9-1bed-4ada-9212-a65bc0c6d878
-- title:
--   Theta: scale Mixed symm apply
-- statement:
--   The inverse weighting `(scaleMixed K).symm` written as an explicit
--   `ℝ`-linear endomorphism of the mixed space: it fixes the real coordinates and
--   scales each complex coordinate by `(√2)⁻¹`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1898-L1909
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1898-L1909

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.scaleMixed_symm_apply (x : mixedSpace K) :
    (scaleMixed K).symm x = (x.1, (Real.sqrt 2)⁻¹ • x.2) := by sorry
