-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_measure_normEqOneSurface_lt_top
-- name    : DedekindZeta.ConeRadialReduction.measure_normEqOneSurface_lt_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:28:30.953403+00:00
-- url     : https://prove2.me/theorems/f0566312-3213-4190-a557-b1faf89799ca
-- title:
--   Cone Radial Reduction: measure norm Eq One Surface lt top
-- statement:
--   **Finiteness of the surface measure of the norm-1 surface.** The surface
--   measure `μ_S = surfaceMeasure K` (the `dr/r`-collar pushforward of the cone Haar
--   measure) assigns finite mass to the relatively compact norm-1 surface
--   fundamental domain, so the constant `1` is `μ_S`-integrable on it (and
--   `∫_S 1 dμ_S = V = surfaceVolume K`). the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1017-L1077
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1017-L1077

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

theorem DedekindZeta.ConeRadialReduction.measure_normEqOneSurface_lt_top :
    surfaceMeasure K (normEqOneSurface K) < ⊤ := by sorry
