-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_norm_mixedEmbedding_ne_zero
-- name    : DedekindZeta.GammaIntegral.norm_mixedEmbedding_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:34:36.907236+00:00
-- url     : https://prove2.me/theorems/ca7e8391-0972-4c61-a8ec-60e56be2176d
-- title:
--   Gamma Integral: norm mixed Embedding ne zero
-- statement:
--   For `a ≠ 0` the Minkowski embedding `σ a = mixedEmbedding K a` has nonzero
--   archimedean norm, hence lies in the multiplicative group `K_ℝ^*`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1404-L1409
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1404-L1409

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
variable {K}

theorem DedekindZeta.GammaIntegral.norm_mixedEmbedding_ne_zero {a : 𝓞 K} (ha : a ≠ 0) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K)) ≠ 0 := by sorry
