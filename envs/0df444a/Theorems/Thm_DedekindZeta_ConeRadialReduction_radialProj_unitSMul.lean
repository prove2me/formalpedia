-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_unitSMul
-- name    : DedekindZeta.ConeRadialReduction.radialProj_unitSMul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:45.080259+00:00
-- url     : https://prove2.me/theorems/d16ab3f3-72bf-407d-a4cc-108abc477e80
-- title:
--   Cone Radial Reduction: radial Proj unit SMul
-- statement:
--   **Radial projection is unit-equivariant.** `radialProj K (u • x) = u • radialProj K x`,
--   since the unit action preserves the norm (`Theta.norm_unitSMul`) and real scaling
--   commutes with the multiplicative unit action (`Algebra.mul_smul_comm`).
--   the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2406-L2410
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2406-L2410

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

theorem DedekindZeta.ConeRadialReduction.radialProj_unitSMul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    radialProj K (u • x) = u • radialProj K x := by sorry
