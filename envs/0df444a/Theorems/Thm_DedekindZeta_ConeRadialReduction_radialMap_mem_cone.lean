-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
-- name    : DedekindZeta.ConeRadialReduction.radialMap_mem_cone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:26:31.242184+00:00
-- url     : https://prove2.me/theorems/c91f88af-d99f-468c-8e63-e51270bbd75d
-- title:
--   Cone Radial Reduction: radial Map mem cone
-- statement:
--   The radial scaling preserves the (scale-invariant) fundamental cone:
--   `radialMap K r x ∈ cone` whenever `x ∈ cone` and `r > 0`
--   (`fundamentalCone.smul_mem_of_mem`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L131-L134
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L131-L134

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

theorem DedekindZeta.ConeRadialReduction.radialMap_mem_cone (r : ℝ) (hr : 0 < r) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.fundamentalCone K) :
    radialMap K r x ∈ mixedEmbedding.fundamentalCone K := by sorry
