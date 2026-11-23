-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
-- name    : DedekindZeta.ConeRadialReduction.norm_radialMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:26:07.424823+00:00
-- url     : https://prove2.me/theorems/e1f8c7f1-8acd-4044-84f3-c8ed856049fd
-- title:
--   Cone Radial Reduction: norm radial Map
-- statement:
--   **Norm scaling.** `N (radialMap K r x) = r · N x` for `r > 0`: the radial
--   parameter `r` is exactly the multiplicative factor on `mixedEmbedding.norm`. From
--   `mixedEmbedding.norm_smul` and `(r^{1/d})^d = r`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L115-L120
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L115-L120

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeRadialReduction.norm_radialMap (r : ℝ) (hr : 0 < r) (x : mixedSpace K) :
    mixedEmbedding.norm (radialMap K r x) = r * mixedEmbedding.norm x := by sorry
