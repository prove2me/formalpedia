-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_aestronglyMeasurable_mixedGaussian_mul_norm_cpow
-- name    : DedekindZeta.GammaIntegral.aestronglyMeasurable_mixedGaussian_mul_norm_cpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:18.725798+00:00
-- url     : https://prove2.me/theorems/bf01e5e2-87a3-4111-9885-d62e7eb77f02
-- title:
--   Gamma Integral: aestrongly Measurable mixed Gaussian mul norm cpow
-- statement:
--   **Measurability of the Mellin integrand** `y ↦ g(y·c)·|N(y)|^s` against
--   `mixedMulHaar` (the standard hypothesis for the Bochner change of variables).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1421-L1436
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1421-L1436

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

theorem DedekindZeta.GammaIntegral.aestronglyMeasurable_mixedGaussian_mul_norm_cpow (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    AEStronglyMeasurable
      (fun y : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c) : ℂ) ^ s)
      (mixedMulHaar K) := by sorry
