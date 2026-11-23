-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_measurable_mixedGaussian_comp_mul_norm_cpow
-- name    : DedekindZeta.GammaIntegral.measurable_mixedGaussian_comp_mul_norm_cpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:35:06.51393+00:00
-- url     : https://prove2.me/theorems/ac042fa8-6d1e-4a50-9c89-31907cea78e7
-- title:
--   Gamma Integral: measurable mixed Gaussian comp mul norm cpow
-- statement:
--   **Measurability** of the single shifted Gaussian × norm-power integrand
--   `x ↦ g(x·c)·|N(x)|^s` (the shift acting on the left of the Gaussian's argument).
--   Companion to `aestronglyMeasurable_mixedGaussian_mul_norm_cpow` (which shifts the
--   norm factor instead); needed for the interchange step's `integral_tsum`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1599-L1609
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1599-L1609

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
open scoped nonZeroDivisors
variable {K}

theorem DedekindZeta.GammaIntegral.measurable_mixedGaussian_comp_mul_norm_cpow (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    Measurable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s) := by sorry
