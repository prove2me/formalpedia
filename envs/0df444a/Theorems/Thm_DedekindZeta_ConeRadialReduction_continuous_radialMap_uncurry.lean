-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
-- name    : DedekindZeta.ConeRadialReduction.continuous_radialMap_uncurry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:26:28.46392+00:00
-- url     : https://prove2.me/theorems/9829f86c-8036-4f82-aabd-30dfb46028d1
-- title:
--   Cone Radial Reduction: continuous radial Map uncurry
-- statement:
--   Continuity of the parametrisation `(r, σ) ↦ radialMap K r σ` on `(0,∞) × S`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L137-L140
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L137-L140

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

theorem DedekindZeta.ConeRadialReduction.continuous_radialMap_uncurry :
    Continuous (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2) := by sorry
