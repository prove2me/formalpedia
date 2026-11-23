-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_radialMap
-- name    : DedekindZeta.ConeRadialReduction.radialProj_radialMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:49.346104+00:00
-- url     : https://prove2.me/theorems/657e558f-687c-4985-9c30-d4fece352858
-- title:
--   Cone Radial Reduction: radial Proj radial Map
-- statement:
--   **Radial projection is radial-scale invariant.** For `t > 0`,
--   `radialProj K (radialMap K t x) = radialProj K x`. From `norm_radialMap`
--   (`N (radialMap K t x) = t * N x`) and `radialMap_radialMap`, the rescaling
--   cancels: `(t * N x)⁻¹ * t = (N x)⁻¹`. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2416-L2424
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2416-L2424

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

theorem DedekindZeta.ConeRadialReduction.radialProj_radialMap {t : ℝ} (ht : 0 < t) (x : mixedSpace K) :
    radialProj K (radialMap K t x) = radialProj K x := by sorry
