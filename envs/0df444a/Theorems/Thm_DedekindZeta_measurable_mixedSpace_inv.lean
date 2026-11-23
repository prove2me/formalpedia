-- Prove2me | Theorems.Thm_DedekindZeta_measurable_mixedSpace_inv
-- name    : DedekindZeta.measurable_mixedSpace_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:01.010901+00:00
-- url     : https://prove2.me/theorems/283b5dea-b7f8-4e8f-a5d5-1157ba3ac685
-- title:
--   Dedekind Zeta: measurable mixed Space inv
-- statement:
--   The inversion `x ↦ x⁻¹` of `K_ℝ^*` is measurable (componentwise inverse on
--   the real/complex coordinates of the mixed space).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1173-L1175
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1173-L1175

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.measurable_mixedSpace_inv :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x⁻¹) := by sorry
