-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_collar_lt_top
-- name    : DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_lt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:58.527847+00:00
-- url     : https://prove2.me/theorems/c1fdc184-1641-417c-9148-e49ae5dc6df6
-- title:
--   Cone Radial Reduction: mixed Mul Haar collar lt top
-- statement:
--   **The norm-collar has finite `mixedMulHaar`-measure.** On
--   `C = cone ∩ {N ∈ (1, e]}` the density `(2/π)^{r₂}·(N x)⁻¹` is bounded by the
--   constant `(2/π)^{r₂}` (since `N x > 1`), and `C` is bounded (a scaled copy of
--   `normLeOne K`), so `volume C < ∞` and hence `mixedMulHaar C < ∞`. Extracted from
--   the proof of `measure_normEqOneSurface_lt_top`. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2473-L2517
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2473-L2517

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

theorem DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_lt_top :
    (DedekindZeta.mixedMulHaar K)
        (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) < ⊤ := by sorry
