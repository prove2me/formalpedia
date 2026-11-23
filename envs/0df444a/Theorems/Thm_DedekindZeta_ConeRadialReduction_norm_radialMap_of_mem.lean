-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap_of_mem
-- name    : DedekindZeta.ConeRadialReduction.norm_radialMap_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:27:25.265063+00:00
-- url     : https://prove2.me/theorems/db5639fc-7a1e-408a-a602-77ab9f3f39ff
-- title:
--   Cone Radial Reduction: norm radial Map of mem
-- statement:
--   For `σ` on the norm-1 surface and `r > 0`, `N (radialMap K r σ) = r`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L123-L126
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L123-L126

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

theorem DedekindZeta.ConeRadialReduction.norm_radialMap_of_mem (r : ℝ) (hr : 0 < r) {σ : mixedSpace K}
    (hσ : σ ∈ normEqOneSurface K) :
    mixedEmbedding.norm (radialMap K r σ) = r := by sorry
