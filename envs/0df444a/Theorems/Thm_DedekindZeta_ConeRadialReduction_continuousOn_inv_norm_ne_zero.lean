-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_inv_norm_ne_zero
-- name    : DedekindZeta.ConeRadialReduction.continuousOn_inv_norm_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:46.314093+00:00
-- url     : https://prove2.me/theorems/0923b4da-d54c-4576-9d2b-be88142614b8
-- title:
--   Cone Radial Reduction: continuous On inv norm ne zero
-- statement:
--   **Inversion is continuous on the nonzero-norm locus.** The mixed-space
--   inversion `x ↦ x⁻¹` is componentwise (real/complex) inversion, continuous exactly
--   where every coordinate is nonzero, i.e. where `N x ≠ 0`
--   (`mixedEmbedding.norm_eq_zero_iff`). the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2431-L2466
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2431-L2466

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
variable (K)

theorem DedekindZeta.ConeRadialReduction.continuousOn_inv_norm_ne_zero :
    ContinuousOn (Inv.inv : mixedSpace K → mixedSpace K)
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by sorry
