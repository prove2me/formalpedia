-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
-- name    : DedekindZeta.ConeRadialReduction.surfaceMeasure_apply_compl_normEqOneSurface
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:27:36.213905+00:00
-- url     : https://prove2.me/theorems/9fdd3e39-0816-4982-b71e-90a7d87b1e3b
-- title:
--   Cone Radial Reduction: surface Measure apply compl norm Eq One Surface
-- statement:
--   The surface measure is supported on the norm-1 surface fundamental domain.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L161-L189
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L161-L189

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

theorem DedekindZeta.ConeRadialReduction.surfaceMeasure_apply_compl_normEqOneSurface :
    surfaceMeasure K (normEqOneSurface K)ᶜ = 0 := by sorry
