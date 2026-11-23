-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap
-- name    : DedekindZeta.ConeRadialReduction.radialMap_radialMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:26:37.495988+00:00
-- url     : https://prove2.me/theorems/8c50e48b-cddb-4d70-bf7a-8b9e650266a1
-- title:
--   Cone Radial Reduction: radial Map radial Map
-- statement:
--   **Composition of radial scalings.** For `a, b ≥ 0`,
--   `radialMap K a (radialMap K b x) = radialMap K (a*b) x`. From `smul_smul` and
--   `Real.mul_rpow` (`(a*b)^{1/d} = a^{1/d}·b^{1/d}`). Used to reduce the radial
--   integral over the collar to an integral over `(0,∞)` via the substitution
--   `r = N x · t`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L197-L199
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L197-L199

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

theorem DedekindZeta.ConeRadialReduction.radialMap_radialMap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : mixedSpace K) :
    radialMap K a (radialMap K b x) = radialMap K (a * b) x := by sorry
