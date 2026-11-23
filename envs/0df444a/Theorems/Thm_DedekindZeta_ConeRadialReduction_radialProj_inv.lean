-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_inv
-- name    : DedekindZeta.ConeRadialReduction.radialProj_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:46.015046+00:00
-- url     : https://prove2.me/theorems/33489dff-b7f3-4ef5-a301-923359b8b585
-- title:
--   Cone Radial Reduction: radial Proj inv
-- statement:
--   **Radial projection commutes with inversion.** For `N x ≠ 0`,
--   `(radialProj K x)⁻¹ = radialProj K x⁻¹`. From `radialProj K x = radialMap K (N x)⁻¹ x`,
--   the radial inversion identity `radialMap_inv`, and `N x⁻¹ = (N x)⁻¹`
--   (`DedekindZeta.mixedEmbedding_norm_inv`). the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2394-L2400
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2394-L2400

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

theorem DedekindZeta.ConeRadialReduction.radialProj_inv {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    (radialProj K x)⁻¹ = radialProj K x⁻¹ := by sorry
