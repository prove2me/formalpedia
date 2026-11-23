-- Prove2me | Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
-- name    : DedekindZeta.Theta.mixedGaussianSchwartz_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:51:14.467374+00:00
-- url     : https://prove2.me/theorems/3d97c687-9eb8-4567-ba4b-6cfffb50bfee
-- title:
--   Theta: mixed Gaussian Schwartz apply
-- statement:
--   The Theta construction uses the mixed Gaussian Schwartz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1884-L1891
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1884-L1891

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.mixedGaussianSchwartz_apply {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (v : minkowskiSpace K) :
    mixedGaussianSchwartz K hx v
      = (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ) := by sorry
