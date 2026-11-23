-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_mulHaar_integral_comp_mul_right
-- name    : DedekindZeta.GammaIntegral.mulHaar_integral_comp_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:27.345809+00:00
-- url     : https://prove2.me/theorems/8c3369ce-3cf8-4c52-95ae-39fdbd6b5164
-- title:
--   Gamma Integral: mul Haar integral comp mul right
-- statement:
--   **Mellin-principle right-translation substitution**: the change of variables
--   `x ↦ x·c` (`N(c) ≠ 0`) is measure-preserving for `d^*x`, hence
--   `∫ g(x·c) d^*x = ∫ g(x) d^*x`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1442-L1451
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1442-L1451

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

theorem DedekindZeta.GammaIntegral.mulHaar_integral_comp_mul_right (g : mixedEmbedding.mixedSpace K → ℂ)
    {c : mixedEmbedding.mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g (x * c) ∂(mixedMulHaar K) = ∫ x, g x ∂(mixedMulHaar K) := by sorry
